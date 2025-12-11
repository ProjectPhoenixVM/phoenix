use std::{
    collections::{HashMap, hash_map::Entry},
    convert::Infallible,
    fs::File,
    io::{self, Read as _},
    os::unix::net::UnixListener,
    path::PathBuf,
    sync::{Arc, LazyLock, Mutex, OnceLock},
    thread,
};

use clap::Parser;
use incinerator::{AlignedPage, CompressBase, MemoryDiff, PAGE_SIZE};
use micro_http::{Body, HttpServer, Method, Request, Response, ServerError, StatusCode, Version};
use tracing::{debug, error, info, info_span};

use crate::runtime::{Runtime, UffdHandler};

mod runtime;

enum CompressedDiff {
    Zstd(Vec<u8>),
    Lz4(Vec<u8>),
    Uncompressed(MemoryDiff),
}

struct OnceCompressedDiff {
    inner: LazyLock<MemoryDiff, Box<dyn FnOnce() -> MemoryDiff + Send + Sync + 'static>>,
}

impl OnceCompressedDiff {
    fn new(diff: CompressedDiff) -> Self {
        Self {
            inner: LazyLock::new(Box::new(move || match diff {
                CompressedDiff::Zstd(items) => {
                    let diff = incinerator::decompress::decompress_zstd(&*items)
                        .expect("Diff was compressed correctly");
                    MemoryDiff::read_from_slice(&*diff).expect("Diff was compressed correctly")
                }
                CompressedDiff::Lz4(items) => {
                    let diff = incinerator::decompress::decompress_lz4(&*items)
                        .expect("Diff was compressed correctly");
                    MemoryDiff::read_from_slice(&*diff).expect("Diff was compressed correctly")
                }
                CompressedDiff::Uncompressed(memory_diff) => memory_diff,
            })),
        }
    }

    fn get(&self) -> &MemoryDiff {
        &self.inner
    }
}

static BASE_PAGES: OnceLock<&'static [AlignedPage]> = OnceLock::new();
static COMPRESS_BASE: OnceLock<CompressBase<'static>> = OnceLock::new();
static DIFFS: LazyLock<Mutex<HashMap<PathBuf, Arc<OnceCompressedDiff>>>> =
    LazyLock::new(Default::default);

pub fn read_pages(mut file: File) -> anyhow::Result<Box<[AlignedPage]>> {
    let file_len = file.metadata()?.len();
    if !file_len.is_multiple_of(PAGE_SIZE as _) {
        anyhow::bail!("File should be a multiple of {PAGE_SIZE}");
    }
    let mut pages = Vec::with_capacity(file_len as usize / PAGE_SIZE);
    let mut buf = AlignedPage::default();
    loop {
        let res = file.read_exact(&mut *buf);
        if let Err(e) = res {
            if e.kind() == io::ErrorKind::UnexpectedEof {
                break;
            }
            return Err(e.into());
        }
        pages.push(buf);
    }
    Ok(pages.into_boxed_slice())
}

#[derive(Parser)]
struct StartupArgs {
    control_api_socket: PathBuf,
    base_snapshot: PathBuf,
}

fn main() -> anyhow::Result<()> {
    use tracing_subscriber::fmt::{self, format::FmtSpan};
    fmt::fmt().with_span_events(FmtSpan::CLOSE).init();

    let args = StartupArgs::parse();
    let mut server = HttpServer::new(&args.control_api_socket).map_err(|e| anyhow::anyhow!(e))?;
    info!(
        "Started HTTP server on socket {:?}",
        args.control_api_socket
    );
    server.start_server().unwrap();

    let base_pages =
        info_span!("base_reading").in_scope(|| read_pages(File::open(args.base_snapshot)?))?;
    BASE_PAGES
        .set(Box::leak(base_pages))
        .map_err(|_| ())
        .expect("BASE_PAGES should not have been set yet");

    let compress_base = info_span!("base_preprocessing")
        .in_scope(|| CompressBase::new(BASE_PAGES.get().unwrap(), rand::rng()));
    COMPRESS_BASE
        .set(compress_base)
        .map_err(|_| ())
        .expect("COMPRESS_BASE should not have been set yet");

    loop {
        let request_vec = match server.requests() {
            Ok(vec) => vec,
            Err(ServerError::ShutdownEvent) => {
                server.flush_outgoing_writes();
                debug!("shutdown request received, API server thread ending.");
                return Ok(());
            }
            Err(err) => {
                error!("API Server error on retrieving incoming request: {}", err);
                continue;
            }
        };
        for server_request in request_vec {
            let response = server_request.process(|request| {
                handle_request(request).unwrap_or_else(|err| {
                    let mut res = Response::new(Version::Http11, StatusCode::BadRequest);
                    res.set_body(Body::new(err.to_string()));
                    res
                })
            });
            if let Err(err) = server.respond(response) {
                error!("API Server encountered an error on response: {}", err);
            };
        }
    }
}

#[derive(Debug, Default, Clone, Copy, serde::Deserialize)]
pub enum RecompressMode {
    #[default]
    None,
    Zstd,
    Lz4,
}

#[derive(Debug, serde::Deserialize)]
struct LoadSnapshotParams {
    #[serde(default = "RecompressMode::default")]
    recompress_method: RecompressMode,
    path: PathBuf,
}

#[derive(Debug, Default, Clone, Copy, serde::Deserialize)]
pub enum LoadType {
    Eager,
    #[default]
    Lazy,
}

#[derive(Debug, serde::Deserialize)]
struct CreateUffdServer {
    uffd_socket: PathBuf,
    snapshot_path: PathBuf,
    #[serde(default = "LoadType::default")]
    load_type: LoadType,
}

#[tracing::instrument(skip_all)]
fn handle_request(request: &Request) -> anyhow::Result<Response> {
    let body = request
        .body
        .as_ref()
        .ok_or(anyhow::anyhow!("Request body is empty"))?;
    match (request.method(), request.uri().get_abs_path()) {
        (Method::Put, "/load") => {
            let params = serde_json::from_slice::<LoadSnapshotParams>(body.raw())?;
            dbg!(&params);

            let mut diffs = DIFFS.lock().unwrap();
            let entry = diffs.entry(params.path.clone());
            if matches!(entry, Entry::Occupied(_)) {
                anyhow::bail!("Entry already exists");
            }

            let deriv_pages =
                info_span!("read_deriv_pages").in_scope(|| read_pages(File::open(params.path)?))?;
            assert_eq!(
                BASE_PAGES.get().unwrap().len(),
                deriv_pages.len(),
                "Derivative snapshots should be the same size as their base"
            );
            let recompressed = info_span!("compress_deriv_snapshot").in_scope(|| {
                let mut diff = COMPRESS_BASE.get().unwrap().compress_pages(&*deriv_pages);
                match params.recompress_method {
                    RecompressMode::None => {
                        diff.shrink_to_fit();
                        CompressedDiff::Uncompressed(diff)
                    }
                    RecompressMode::Zstd => CompressedDiff::Zstd(
                        incinerator::compress::write_zstd(&diff).expect("Encoding should succeed"),
                    ),
                    RecompressMode::Lz4 => CompressedDiff::Lz4(
                        incinerator::compress::write_lz4(&diff).expect("Encoding should succeed"),
                    ),
                }
            });
            entry.insert_entry(Arc::new(OnceCompressedDiff::new(recompressed)));
            Ok(Response::new(Version::Http11, StatusCode::OK))
        }
        (Method::Put, "/create_uffd_server") => {
            let params = serde_json::from_slice::<CreateUffdServer>(body.raw())?;
            dbg!(&params);

            let diffs = DIFFS.lock().unwrap();
            let Some(diff) = diffs.get(&params.snapshot_path) else {
                anyhow::bail!("Given shapshot path is not loaded yet");
            };

            let diff = Arc::clone(diff);
            drop(diffs);

            thread::spawn(move || match params.load_type {
                LoadType::Eager => eager_fault_handler(params.uffd_socket, diff),
                LoadType::Lazy => lazy_fault_handler(params.uffd_socket, diff),
            });

            Ok(Response::new(Version::Http11, StatusCode::OK))
        }
        _ => Err(anyhow::anyhow!("Unknown endpoint")),
    }
}

fn eager_fault_handler(socket: PathBuf, diff: Arc<OnceCompressedDiff>) -> Infallible {
    let listener = UnixListener::bind(socket).expect("Cannot bind to socket path");
    let (stream, _) = listener.accept().expect("Cannot listen on UDS socket");
    let mut runtime = Runtime::new(stream, diff);

    runtime.install_panic_hook();
    runtime.run(|uffd_handler: &mut UffdHandler| {
        // Read an event from the userfaultfd.
        let event = uffd_handler
            .read_event()
            .expect("Failed to read uffd_msg")
            .expect("uffd_msg not ready");

        match event {
            userfaultfd::Event::Pagefault { .. } => {
                for region in uffd_handler.mem_regions.clone() {
                    for page in (0..region.size).step_by(PAGE_SIZE) {
                        uffd_handler
                            .serve_pf((region.base_host_virt_addr as usize + page) as _, PAGE_SIZE);
                    }
                }
            }
            _ => panic!("Unexpected event on userfaultfd"),
        }
    })
}

fn lazy_fault_handler(socket: PathBuf, diff: Arc<OnceCompressedDiff>) -> Infallible {
    let listener = UnixListener::bind(socket).expect("Cannot bind to socket path");
    let (stream, _) = listener.accept().expect("Cannot listen on UDS socket");
    let mut runtime = Runtime::new(stream, diff);

    runtime.install_panic_hook();
    runtime.run(|uffd_handler: &mut UffdHandler| {
        let mut deferred_events = Vec::new();

        loop {
            // First, try events that we couldn't handle last round
            let mut events_to_handle = Vec::from_iter(deferred_events.drain(..));

            // Read all events from the userfaultfd.
            while let Some(event) = uffd_handler.read_event().expect("Failed to read uffd_msg") {
                events_to_handle.push(event);
            }

            for event in events_to_handle.drain(..) {
                // We expect to receive either a Page Fault or `remove`
                // event (if the balloon device is enabled).
                match event {
                    userfaultfd::Event::Pagefault { addr, .. } => {
                        if !uffd_handler.serve_pf(addr.cast(), PAGE_SIZE) {
                            deferred_events.push(event);
                        }
                    }
                    userfaultfd::Event::Remove { start, end } => {
                        uffd_handler.unregister_range(start, end)
                    }
                    _ => panic!("Unexpected event on userfaultfd"),
                }
            }

            // We assume that really only the above removed/pagefault interaction can result in
            // deferred events. In that scenario, the loop will always terminate (unless
            // newly arriving `remove` events end up indefinitely blocking it, but there's nothing
            // we can do about that, and it's a largely theoretical problem).
            if deferred_events.is_empty() {
                break;
            }
        }
    })
}

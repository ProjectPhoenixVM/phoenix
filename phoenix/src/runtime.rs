#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::undocumented_unsafe_blocks,
    // Not everything is used by both binaries
    dead_code
)]

use std::collections::HashMap;
use std::convert::Infallible;
use std::ffi::c_void;
use std::fs::File;
use std::os::unix::io::{AsRawFd, FromRawFd, IntoRawFd};
use std::os::unix::net::UnixStream;
use std::ptr;
use std::sync::Arc;
use std::time::Duration;

use incinerator::{AlignedPage, PAGE_SIZE};
use serde::{Deserialize, Serialize};
use userfaultfd::{Error, Event, Uffd};
use vmm_sys_util::sock_ctrl_msg::ScmSocket;

use crate::{BASE_PAGES, OnceCompressedDiff};

// This is the same with the one used in src/vmm.
/// This describes the mapping between Firecracker base virtual address and offset in the
/// buffer or file backend for a guest memory region. It is used to tell an external
/// process/thread where to populate the guest memory data for this range.
///
/// E.g. Guest memory contents for a region of `size` bytes can be found in the backend
/// at `offset` bytes from the beginning, and should be copied/populated into `base_host_address`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GuestRegionUffdMapping {
    /// Base host virtual address where the guest memory contents for this region
    /// should be copied/populated.
    pub base_host_virt_addr: u64,
    /// Region size.
    pub size: usize,
    /// Offset in the backend file/buffer where the region contents are.
    pub offset: u64,
    /// The configured page size for this memory region.
    pub page_size: usize,
}

impl GuestRegionUffdMapping {
    fn contains(&self, fault_page_addr: u64) -> bool {
        fault_page_addr >= self.base_host_virt_addr
            && fault_page_addr < self.base_host_virt_addr + self.size as u64
    }
}

pub struct UffdHandler {
    pub mem_regions: Vec<GuestRegionUffdMapping>,
    diff: Arc<OnceCompressedDiff>,
    uffd: Uffd,
}

impl UffdHandler {
    fn try_get_mappings_and_file(
        stream: &UnixStream,
    ) -> Result<(String, Option<File>), std::io::Error> {
        let mut message_buf = vec![0u8; 1024];
        let (bytes_read, file) = stream.recv_with_fd(&mut message_buf[..])?;
        message_buf.resize(bytes_read, 0);

        // We do not expect to receive non-UTF-8 data from Firecracker, so this is probably
        // an error we can't recover from. Just immediately abort
        let body = String::from_utf8(message_buf.clone()).unwrap_or_else(|_| {
            panic!(
                "Received body is not a utf-8 valid string. Raw bytes received: {message_buf:#?}"
            )
        });
        Ok((body, file))
    }

    fn get_mappings_and_file(stream: &UnixStream) -> (String, File) {
        // Sometimes, reading from the stream succeeds but we don't receive any
        // UFFD descriptor. We don't really have a good understanding why this is
        // happening, but let's try to be a bit more robust and retry a few times
        // before we declare defeat.
        for _ in 1..=5 {
            match Self::try_get_mappings_and_file(stream) {
                Ok((body, Some(file))) => {
                    return (body, file);
                }
                Ok((body, None)) => {
                    println!("Didn't receive UFFD over socket. We received: '{body}'. Retrying...");
                }
                Err(err) => {
                    println!("Could not get UFFD and mapping from Firecracker: {err}. Retrying...");
                }
            }
            std::thread::sleep(Duration::from_millis(100));
        }

        panic!("Could not get UFFD and mappings after 5 retries");
    }

    pub fn from_unix_stream(stream: &UnixStream, diff: Arc<OnceCompressedDiff>) -> Self {
        let (body, file) = Self::get_mappings_and_file(stream);
        let mappings =
            serde_json::from_str::<Vec<GuestRegionUffdMapping>>(&body).unwrap_or_else(|_| {
                panic!("Cannot deserialize memory mappings. Received body: {body}")
            });
        let memsize: usize = mappings.iter().map(|r| r.size).sum();
        // Page size is the same for all memory regions, so just grab the first one
        let first_mapping = mappings.first().unwrap_or_else(|| {
            panic!(
                "Cannot get the first mapping. Mappings size is {}. Received body: {body}",
                mappings.len()
            )
        });
        let page_size = first_mapping.page_size;
        assert_eq!(
            page_size, PAGE_SIZE,
            "The only supported page size is {}",
            PAGE_SIZE,
        );

        // Make sure memory size matches backing data size.
        assert_eq!(
            memsize,
            BASE_PAGES.get().unwrap().len() * PAGE_SIZE,
            "Guest region has a different size to diff snapshot"
        );

        let uffd = unsafe { Uffd::from_raw_fd(file.into_raw_fd()) };

        Self {
            mem_regions: dbg!(mappings),
            diff,
            uffd,
        }
    }

    pub fn read_event(&mut self) -> Result<Option<Event>, Error> {
        self.uffd.read_event()
    }

    pub fn unregister_range(&mut self, start: *mut c_void, end: *mut c_void) {
        assert!(
            (start as usize).is_multiple_of(PAGE_SIZE)
                && (end as usize).is_multiple_of(PAGE_SIZE)
                && end > start
        );
        // SAFETY: start and end are valid and provided by UFFD
        let len = unsafe { end.offset_from_unsigned(start) };
        self.uffd
            .unregister(start, len)
            .expect("range should be valid");
    }

    pub fn serve_pf(&mut self, addr: *mut u8, len: usize) -> bool {
        // Find the start of the page that the current faulting address belongs to.
        let dst = (addr as usize & !(PAGE_SIZE - 1)) as *mut libc::c_void;
        let fault_page_addr = dst as u64;

        for region in self.mem_regions.iter() {
            if region.contains(fault_page_addr) {
                return self.populate_from_diff(region, fault_page_addr, len);
            }
        }

        panic!(
            "Could not find addr: {:?} within guest region mappings.",
            addr
        );
    }

    fn populate_from_diff(&self, region: &GuestRegionUffdMapping, dst: u64, len: usize) -> bool {
        let base_pages = BASE_PAGES.get().unwrap();
        let offset = dst - region.base_host_virt_addr;

        let source_byte_index = region.offset + offset;
        assert!(source_byte_index.is_multiple_of(PAGE_SIZE as u64));

        let source_page_index = source_byte_index / (PAGE_SIZE as u64);
        assert_eq!(len, PAGE_SIZE, "Only supports faulting one page at a time");
        assert!(source_page_index <= base_pages.len() as u64);

        let mut page_buf = AlignedPage::default();
        let decompressed_page = self
            .diff
            .get()
            .get_page(base_pages, source_page_index as u32, &mut page_buf)
            .unwrap();

        unsafe {
            match self.uffd.copy(
                &raw const **decompressed_page as *const _,
                dst as *mut _,
                len,
                true,
            ) {
                // Make sure the UFFD copied some bytes.
                Ok(value) => assert!(value > 0),
                // Catch EAGAIN errors, which occur when a `remove` event lands in the UFFD
                // queue while we're processing `pagefault` events.
                // The weird cast is because the `bytes_copied` field is based on the
                // `uffdio_copy->copy` field, which is a signed 64 bit integer, and if something
                // goes wrong, it gets set to a -errno code. However, uffd-rs always casts this
                // value to an unsigned `usize`, which scrambled the errno.
                Err(Error::PartiallyCopied(bytes_copied))
                    if bytes_copied == 0 || bytes_copied == (-libc::EAGAIN) as usize =>
                {
                    return false;
                }
                Err(Error::CopyFailed(errno))
                    if std::io::Error::from(errno).raw_os_error().unwrap() == libc::EEXIST => {}
                Err(e) => {
                    panic!("Uffd copy failed: {e:?}");
                }
            }
        };

        true
    }
}

pub struct Runtime {
    stream: UnixStream,
    diff: Arc<OnceCompressedDiff>,
    uffds: HashMap<i32, UffdHandler>,
}

impl Runtime {
    pub fn new(stream: UnixStream, diff: Arc<OnceCompressedDiff>) -> Self {
        Self {
            stream,
            diff,
            uffds: HashMap::default(),
        }
    }

    fn peer_process_credentials(&self) -> libc::ucred {
        let mut creds: libc::ucred = libc::ucred {
            pid: 0,
            gid: 0,
            uid: 0,
        };
        let mut creds_size = size_of::<libc::ucred>() as u32;
        let ret = unsafe {
            libc::getsockopt(
                self.stream.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_PEERCRED,
                (&raw mut creds).cast::<c_void>(),
                &raw mut creds_size,
            )
        };
        if ret != 0 {
            panic!("Failed to get peer process credentials");
        }
        creds
    }

    pub fn install_panic_hook(&self) {
        let peer_creds = self.peer_process_credentials();

        let default_panic_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |panic_info| {
            let r = unsafe { libc::kill(peer_creds.pid, libc::SIGKILL) };

            if r != 0 {
                eprintln!("Failed to kill Firecracker process from panic hook");
            }

            default_panic_hook(panic_info);
        }));
    }

    /// Polls the `UnixStream` and UFFD fds in a loop.
    /// When stream is polled, new uffd is retrieved.
    /// When uffd is polled, page fault is handled by
    /// calling `pf_event_dispatch` with corresponding
    /// uffd object passed in.
    pub fn run(&mut self, pf_event_dispatch: impl Fn(&mut UffdHandler)) -> Infallible {
        let mut pollfds = vec![];

        // Poll the stream for incoming uffds
        pollfds.push(libc::pollfd {
            fd: self.stream.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        });

        loop {
            let pollfd_ptr = pollfds.as_mut_ptr();
            let pollfd_size = pollfds.len() as u64;

            // # Safety:
            // Pollfds vector is valid
            let mut nready = unsafe { libc::poll(pollfd_ptr, pollfd_size, -1) };

            if nready == -1 {
                panic!("Could not poll for events!")
            }

            for i in 0..pollfds.len() {
                if nready == 0 {
                    break;
                }
                if pollfds[i].revents & libc::POLLIN != 0 {
                    nready -= 1;
                    if pollfds[i].fd == self.stream.as_raw_fd() {
                        // Handle new uffd from stream
                        let handler =
                            UffdHandler::from_unix_stream(&self.stream, Arc::clone(&self.diff));
                        pollfds.push(libc::pollfd {
                            fd: handler.uffd.as_raw_fd(),
                            events: libc::POLLIN,
                            revents: 0,
                        });
                        self.uffds.insert(handler.uffd.as_raw_fd(), handler);
                    } else {
                        // Handle one of uffd page faults
                        pf_event_dispatch(self.uffds.get_mut(&pollfds[i].fd).unwrap());
                    }
                }
            }
            // If connection is closed, we can skip the socket from being polled.
            pollfds.retain(|pollfd| pollfd.revents & (libc::POLLRDHUP | libc::POLLHUP) == 0);
        }
    }
}

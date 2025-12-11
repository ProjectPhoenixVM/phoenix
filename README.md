Phoenix and Incinerator
===

Fast MicroVM page fault handler and memory compression library

## Run instructions
Set up firecracker using [their docs](https://github.com/firecracker-microvm/firecracker?tab=readme-ov-file#getting-started)

Build phoenix: `cd phoenix && cargo build --release && cp ./target/release/phoenix .. && cd ..`

Use [our scripts](https://github.com/ProjectPhoenixVM/Firecracker-scripts) to setup and run firecracker with different configurations:

Run firecracker normally:
in one terminal, run `start_firecracker.bash`, then in another do `configure_vm.bash && start_vm.bash`

(to kill a firecracker instance use `reboot` from its terminal)

To take a snapshot of a vm:
`pause_vm.bash && make_snapshot.bash` (you can also then resume it with `resume_vm.bash`)

To load a snapshot using KVM fault handler (Assuming the snapshot file is `/path/to/foobar_snapshot` and the memory file is `/path/to/foobar`):
in one terminal, run `start_firecracker.bash`, then in another do `load_snapshot.bash /path/to/foobar && resume_vm.bash`

To load a snapshot using phoenix (Assume the base memory snapshot is `/path/to/foo`, ther derivitive memory file is `/path/to/foobar`, and the derivitive snapshot file is `/path/to/foobar_snapshot`):
in one terminal, run `sudo reset.bash && ./phoenix /tmp/uffd_control.socket /path/to/foobar` (this only loads the base snapshot into memory);
in another terminal run `start_firecracker.bash`;
in another terminal run `configure_phoenix.bash /path/to/foobar` (this loads and diff-compresses the derivitive snapshot), then `load_uffd.bash /path/to/foobar_snapshot && resume_vm.bash`

You can also use a file-backed uffd handler (assume the same snapshot locations as for phoenix):
Build [the handler](https://github.com/ProjectPhoenixVM/File-UFFD-hander) with `cargo build --release` and copy the executable from `/target/release/uffd`
in one terminal, run `sudo reset.bash && ./uffd /tmp/firecracker_uffd.socket /path/to/foobar`;
in another terminal run `start_firecracker.bash`;
in another terminal run `load_uffd.bash /path/to/foobar_snapshot && resume_vm.bash`

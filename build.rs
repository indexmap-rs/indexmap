extern crate autocfg;

fn main() {
    //let ac = autocfg::new();
    //ac.emit_sysroot_crate("std");
    //ac.emit_sysroot_crate("alloc");
    autocfg::emit("std");
    //autocfg::emit("alloc");
}

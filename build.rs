fn main() {
    let ac = autocfg::new();
    ac.emit_has_path("std");
    ac.emit_has_path("alloc");
}
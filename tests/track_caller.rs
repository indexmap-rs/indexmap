//! Panics from the index-taking `IndexMap` entry points must name the caller.
//!
//! This is its own test binary because it replaces the global panic hook.

use indexmap::IndexMap;
use indexmap::map::Entry;

#[test]
fn vacant_entry_shift_insert_oob_reports_the_caller() {
    let file = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
    let hook_file = std::sync::Arc::clone(&file);
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        if let Some(loc) = info.location() {
            *hook_file.lock().unwrap() = String::from(loc.file());
        }
    }));
    let caught = std::panic::catch_unwind(|| {
        let mut map: IndexMap<u32, u32> = IndexMap::new();
        map.insert(0, 0);
        let Entry::Vacant(entry) = map.entry(1) else {
            unreachable!()
        };
        entry.shift_insert(5, 10);
    });
    std::panic::set_hook(prev);
    assert!(caught.is_err());
    let file = file.lock().unwrap().clone();
    assert!(
        file.ends_with("track_caller.rs"),
        "panic reported at {file}"
    );
}

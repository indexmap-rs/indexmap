use debugger_test::debugger_test;
use indexmap::IndexMap;
use indexmap::IndexSet;

#[inline(never)]
fn __break() {}

#[debugger_test(
    debugger = "cdb",
    commands = r#"
.nvlist
dx set
dx map
"#,
    expected_statements = r#"
set              : { len=0x63 } [Type: indexmap::set::IndexSet<i32,std::collections::hash::map::RandomState>]
[len]            : 0x63 [Type: unsigned __int64]
[0]              : 0 [Type: indexmap::Bucket<i32,tuple$<> >]
[1]              : 1 [Type: indexmap::Bucket<i32,tuple$<> >]
[98]             : 98 [Type: indexmap::Bucket<i32,tuple$<> >]

map              : { len=0x63 } [Type: indexmap::map::IndexMap<i32,i32,std::collections::hash::map::RandomState>]
[len]            : 0x63 [Type: unsigned __int64]
[0]              : { key=0, value=0 } [Type: indexmap::Bucket<i32,i32>]
[1]              : { key=1, value=-1 } [Type: indexmap::Bucket<i32,i32>]
[2]              : { key=2, value=-2 } [Type: indexmap::Bucket<i32,i32>]
[98]             : { key=98, value=-98 } [Type: indexmap::Bucket<i32,i32>]
"#
)]
fn test_debugger_visualizer() {
    let mut set = IndexSet::new();
    let mut map = IndexMap::new();

    for i in 0..100 {
        set.insert(i);
        map.insert(i, -i);
    }

    let key = 99;
    assert!(set.shift_remove(&key));
    assert_eq!(Some(-99), map.remove(&key));

    __break();
}

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
set              : { len=0x19 } [Type: indexmap::set::IndexSet<char,std::collections::hash::map::RandomState>]
    [len]            : 0x19 [Type: unsigned __int64]
    [capacity]       : 0x1c [Type: unsigned __int64]
    [0]              : 0x74 't' [Type: indexmap::Bucket<char,tuple$<> >]
    [1]              : 0x68 'h' [Type: indexmap::Bucket<char,tuple$<> >]
    [2]              : 0x65 'e' [Type: indexmap::Bucket<char,tuple$<> >]
    [3]              : 0x20 ' ' [Type: indexmap::Bucket<char,tuple$<> >]
    [4]              : 0x71 'q' [Type: indexmap::Bucket<char,tuple$<> >]
    [5]              : 0x75 'u' [Type: indexmap::Bucket<char,tuple$<> >]
    [6]              : 0x69 'i' [Type: indexmap::Bucket<char,tuple$<> >]
    [7]              : 0x63 'c' [Type: indexmap::Bucket<char,tuple$<> >]
    [8]              : 0x6b 'k' [Type: indexmap::Bucket<char,tuple$<> >]
    [9]              : 0x72 'r' [Type: indexmap::Bucket<char,tuple$<> >]
    [10]             : 0x6f 'o' [Type: indexmap::Bucket<char,tuple$<> >]
    [11]             : 0x77 'w' [Type: indexmap::Bucket<char,tuple$<> >]
    [12]             : 0x6e 'n' [Type: indexmap::Bucket<char,tuple$<> >]
    [13]             : 0x66 'f' [Type: indexmap::Bucket<char,tuple$<> >]
    [14]             : 0x78 'x' [Type: indexmap::Bucket<char,tuple$<> >]
    [15]             : 0x6a 'j' [Type: indexmap::Bucket<char,tuple$<> >]
    [16]             : 0x6d 'm' [Type: indexmap::Bucket<char,tuple$<> >]
    [17]             : 0x70 'p' [Type: indexmap::Bucket<char,tuple$<> >]
    [18]             : 0x64 'd' [Type: indexmap::Bucket<char,tuple$<> >]
    [19]             : 0x76 'v' [Type: indexmap::Bucket<char,tuple$<> >]
    [20]             : 0x6c 'l' [Type: indexmap::Bucket<char,tuple$<> >]
    [21]             : 0x61 'a' [Type: indexmap::Bucket<char,tuple$<> >]
    [22]             : 0x7a 'z' [Type: indexmap::Bucket<char,tuple$<> >]
    [23]             : 0x79 'y' [Type: indexmap::Bucket<char,tuple$<> >]
    [24]             : 0x67 'g' [Type: indexmap::Bucket<char,tuple$<> >]

map              : { len=0x19 } [Type: indexmap::map::IndexMap<char,i32,std::collections::hash::map::RandomState>]
    [len]            : 0x19 [Type: unsigned __int64]
    [capacity]       : 0x1c [Type: unsigned __int64]
    [0]              : { key=0x74 't', value=2 } [Type: indexmap::Bucket<char,i32>]
    [1]              : { key=0x68 'h', value=2 } [Type: indexmap::Bucket<char,i32>]
    [2]              : { key=0x65 'e', value=4 } [Type: indexmap::Bucket<char,i32>]
    [3]              : { key=0x20 ' ', value=8 } [Type: indexmap::Bucket<char,i32>]
    [4]              : { key=0x71 'q', value=1 } [Type: indexmap::Bucket<char,i32>]
    [5]              : { key=0x75 'u', value=2 } [Type: indexmap::Bucket<char,i32>]
    [6]              : { key=0x69 'i', value=1 } [Type: indexmap::Bucket<char,i32>]
    [7]              : { key=0x63 'c', value=1 } [Type: indexmap::Bucket<char,i32>]
    [8]              : { key=0x6b 'k', value=1 } [Type: indexmap::Bucket<char,i32>]
    [9]              : { key=0x67 'g', value=1 } [Type: indexmap::Bucket<char,i32>]
    [10]             : { key=0x72 'r', value=2 } [Type: indexmap::Bucket<char,i32>]
    [11]             : { key=0x6f 'o', value=4 } [Type: indexmap::Bucket<char,i32>]
    [12]             : { key=0x77 'w', value=1 } [Type: indexmap::Bucket<char,i32>]
    [13]             : { key=0x6e 'n', value=1 } [Type: indexmap::Bucket<char,i32>]
    [14]             : { key=0x66 'f', value=1 } [Type: indexmap::Bucket<char,i32>]
    [15]             : { key=0x78 'x', value=1 } [Type: indexmap::Bucket<char,i32>]
    [16]             : { key=0x6a 'j', value=1 } [Type: indexmap::Bucket<char,i32>]
    [17]             : { key=0x6d 'm', value=1 } [Type: indexmap::Bucket<char,i32>]
    [18]             : { key=0x70 'p', value=1 } [Type: indexmap::Bucket<char,i32>]
    [19]             : { key=0x64 'd', value=2 } [Type: indexmap::Bucket<char,i32>]
    [20]             : { key=0x76 'v', value=1 } [Type: indexmap::Bucket<char,i32>]
    [21]             : { key=0x6c 'l', value=1 } [Type: indexmap::Bucket<char,i32>]
    [22]             : { key=0x61 'a', value=1 } [Type: indexmap::Bucket<char,i32>]
    [23]             : { key=0x7a 'z', value=1 } [Type: indexmap::Bucket<char,i32>]
    [24]             : { key=0x79 'y', value=1 } [Type: indexmap::Bucket<char,i32>]
"#
)]
fn test_debugger_visualizer() {
    let mut set = IndexSet::new();
    let mut map = IndexMap::new();

    for ch in "the quick brown fox jumped over the lazy dog".chars() {
        set.insert(ch);
        *map.entry(ch).or_insert(0) += 1;
    }

    let b = 'b';
    assert!(set.shift_remove(&b));
    assert_eq!(Some(1), map.remove(&b));

    __break();
}

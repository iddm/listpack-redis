use listpack_redis::*;

fn main() {
    let mut listpack: Listpack = Listpack::default();
    listpack.push("hello");
    listpack.push("world");

    let entry = listpack.get(0).unwrap();
    assert_eq!(entry.to_string(), "hello");

    let entry = &listpack[1];
    assert_eq!(entry.to_string(), "world");

    listpack.replace(1, "rust");
    let entry = &listpack[1];
    assert_eq!(entry.to_string(), "rust");

    listpack.remove(0);
    let entry = &listpack[0];
    assert_eq!(entry.to_string(), "rust");

    listpack.clear();
    assert_eq!(listpack.len(), 0);
    assert!(listpack.is_empty());
}

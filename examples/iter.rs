use listpack_redis::*;

fn main() {
    let mut listpack: Listpack = Listpack::default();
    listpack.push("hello");
    listpack.push("world");

    // The default Rust implementation of the Iterator trait.
    listpack.iter().for_each(|entry| {
        println!("Entry: {entry}");
    });

    let world_entry = listpack.iter().find(|entry| *entry == "world").unwrap();

    assert_eq!(world_entry.to_string(), "world");

    listpack.windows(2).for_each(|window| {
        println!("Window: {window:?}");
    });

    // TODO: uncomment this when the drain method is implemented.
    // listpack.drain(0..1).for_each(|removed| {
    //     println!("Drained entry: {removed}");
    // });

    assert_eq!(listpack.len(), 1);
    assert_eq!(listpack.get(0).unwrap().to_string(), "world");

    let mut listpack2 = Listpack::from(&["rust", "is", "the", "best", "in", "the"]);
    listpack2.append(&mut listpack);

    assert_eq!(listpack2.len(), 7);
    assert_eq!(
        listpack2,
        &["rust", "is", "the", "best", "in", "the", "world"]
    );
}

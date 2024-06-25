/// Returns the actual virtual address size of the CPU where the build
/// process is running.
fn get_actual_virtual_address_size() -> Result<u8, &'static str> {
    // Read the /proc/cpuinfo file, find there the value for the
    // "Address sizes" field, and return that number.
    // An example string:
    //
    // "address sizes	: 48 bits physical, 48 bits virtual"
    //
    // we return the number 48.

    let address_sizes = std::fs::read_to_string("/proc/cpuinfo")
        .map_err(|_| "Couldn't read the /proc/cpuinfo file.")?;

    let address_sizes = address_sizes
        .lines()
        .find(|line| line.starts_with("address sizes"))
        .ok_or("The 'address sizes' field is not found in the /proc/cpuinfo file.")?;

    let address_sizes = address_sizes
        .split(':')
        .nth(1)
        .ok_or("The 'address sizes' field is not found in the /proc/cpuinfo file.")?;

    let address_sizes = address_sizes
        .trim()
        .split(',')
        .find(|part| part.contains("virtual"))
        .ok_or("The 'virtual' part is not found in the 'address sizes' field.")?;

    let address_sizes = address_sizes
        .split_whitespace()
        .find(|part| part.parse::<u8>().is_ok())
        .ok_or("The number of bits is not found in the 'address sizes' field.")?;

    let address_size = address_sizes
        .parse::<u8>()
        .map_err(|_| "Couldn't extract the virtual address size value.")?;

    Ok(address_size)
}

fn main() {
    let actual_address_size = get_actual_virtual_address_size().unwrap();
    let maximum_address_size: usize = std::mem::size_of::<usize>() * 8;
    let unused_address_size = maximum_address_size - actual_address_size as usize;

    println!("cargo:rustc-env=VIRTUAL_ADDRESS_UNUSED_SIZE={unused_address_size}");
}

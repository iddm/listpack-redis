use std::env;
use std::io::{stderr, stdout, Write};
use std::path::PathBuf;

const HEADER_FILE_PATH: &str = "redis/src/listpack.h";
const SOURCE_FILE_PATH: &str = "redis/src/listpack.c";
const ZMALLOC_SOURCE_FILE_PATH: &str = "redis/src/zmalloc.c";
const UTIL_SOURCE_FILE_PATH: &str = "redis/src/util.c";
const FPCONV_DTOA_SOURCE_FILE_PATH: &str = "redis/deps/fpconv/fpconv_dtoa.c";

fn compile_file(file_path: &std::path::Path, obj_path: &std::path::Path, include_dirs: &[&str]) {
    let compile_job = std::process::Command::new("clang")
        .arg("-g")
        .arg("-G0")
        .arg("-O3")
        .args([
            "-fdata-sections",
            "-ffunction-sections",
            "-Wl,--gc-sections",
        ])
        .arg("-c")
        .arg("-o")
        .arg(obj_path)
        .arg(file_path)
        .args(include_dirs)
        .output()
        .expect("compile using `clang`");

    if !compile_job.status.success() {
        stdout().write_all(&compile_job.stdout).unwrap();
        stderr().write_all(&compile_job.stderr).unwrap();
    }
}

fn compile_redis_objects_and_link_into_a_library(
    library_name: &str,
    source_files: &[&str],
    include_dirs: &[&str],
    libdir_path: &std::path::Path,
) {
    let root_directory = PathBuf::from(".")
        .canonicalize()
        .expect("cannot canonicalize path");
    let mut object_files = Vec::new();

    for source_file in source_files {
        let obj_path = root_directory.join(format!("{}.o", source_file));
        compile_file(&root_directory.join(source_file), &obj_path, include_dirs);
        object_files.push(obj_path);
    }

    let library_path = libdir_path.join(format!("lib{}.a", library_name));

    // Run `ar` to generate the static library.
    if !std::process::Command::new("ar")
        .arg("rcs")
        .arg(&library_path)
        .args(&object_files)
        .output()
        .expect("could not spawn `ar`")
        .status
        .success()
    {
        // Panic if the command was not successful.
        panic!("could not emit library file");
    }

    // // Strip the unused symbols.
    // if !std::process::Command::new("strip")
    //     .arg(&library_path)
    //     .output()
    //     .expect("could not spawn `strip`")
    //     .status
    //     .success()
    // {
    //     panic!("could not strip the library file");
    // }

    // Link against the built helpers wrapper.
    println!("cargo:rustc-link-search={}", libdir_path.to_str().unwrap());
    println!("cargo:rustc-link-lib={}", library_name);
}

fn compile_helpers() {
    let git_submodule_update_job = std::process::Command::new("git")
        .arg("submodule")
        .arg("update")
        .arg("--init")
        .arg("--recursive")
        .arg("--depth")
        .arg("1")
        .output()
        .expect("run git successfully");

    if !git_submodule_update_job.status.success() {
        let stdout = String::from_utf8(git_submodule_update_job.stdout).unwrap();
        let stderr = String::from_utf8(git_submodule_update_job.stderr).unwrap();
        panic!("could not checkout the submodules.\nStdout:\n{stdout}\n\nStderr:\n{stderr}");
    }

    let libdir_path = PathBuf::from("./target/")
        .canonicalize()
        .expect("cannot canonicalize path");

    let include_dirs = ["-I./redis/deps/fpconv"];

    compile_redis_objects_and_link_into_a_library(
        "listpack",
        &[
            SOURCE_FILE_PATH,
            ZMALLOC_SOURCE_FILE_PATH,
            UTIL_SOURCE_FILE_PATH,
            FPCONV_DTOA_SOURCE_FILE_PATH,
        ],
        &include_dirs,
        &libdir_path,
    );
}

fn generate_bindings() {
    // The bindgen::Builder is the main entry point
    // to bindgen, and lets you build up options for
    // the resulting bindings.
    let bindings = bindgen::Builder::default()
        // The input header we would like to generate
        // bindings for.
        .header(HEADER_FILE_PATH)
        // Tell cargo to invalidate the built crate whenever any of the
        // included header files changed.
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .impl_debug(true)
        .impl_partialeq(true)
        .prepend_enum_name(false)
        .generate_inline_functions(true)
        // .generate_cstr(true)
        .disable_name_namespacing()
        .disable_nested_struct_naming()
        .default_enum_style(bindgen::EnumVariation::Rust {
            non_exhaustive: true,
        })
        // Finish the builder and generate the bindings.
        .generate()
        // Unwrap the Result and panic on failure.
        .expect("Unable to generate bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}

fn main() {
    // Tell cargo to invalidate the built crate whenever the wrapper changes
    // println!("cargo:rerun-if-changed={HEADER_FILE_PATH}");

    compile_helpers();
    generate_bindings();
}

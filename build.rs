use std::env;
use std::path::PathBuf;

const HEADER_FILE_PATH: &str = "src/bindings.h";
const SOURCE_FILE_PATH: &str = "src/bindings.c";

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

    let libdir_path = PathBuf::from("./")
        .canonicalize()
        .expect("cannot canonicalize path");

    let obj_path = libdir_path.join("target/listpack.o");
    let lib_path = libdir_path.join("target/liblistpack.a");

    // Run `clang` to compile the source code file into an object file.
    let compile_job = std::process::Command::new("clang")
        .arg("-g")
        .arg("-G0")
        .arg("-c")
        .arg("-o")
        .arg(&obj_path)
        .arg(libdir_path.join(SOURCE_FILE_PATH))
        .output()
        .expect("compile using `clang`");

    if !compile_job.status.success() {
        let stdout = String::from_utf8(compile_job.stdout).unwrap();
        let stderr = String::from_utf8(compile_job.stderr).unwrap();

        panic!("could not compile object file.\nStdout:\n{stdout}\n\nStderr:\n{stderr}");
    }

    // Run `ar` to generate the static library.
    if !std::process::Command::new("ar")
        .arg("rcs")
        .arg(lib_path)
        .arg(obj_path)
        .output()
        .expect("could not spawn `ar`")
        .status
        .success()
    {
        // Panic if the command was not successful.
        panic!("could not emit library file");
    }

    // Link against the built helpers wrapper.
    println!(
        "cargo:rustc-link-search={}",
        libdir_path.join("target/").to_str().unwrap()
    );
    println!("cargo:rustc-link-lib=listpack");
}

fn main() {
    compile_helpers();

    // Tell cargo to invalidate the built crate whenever the wrapper changes
    println!("cargo:rerun-if-changed={HEADER_FILE_PATH}");

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

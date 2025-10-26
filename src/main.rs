use std::env;
use std::fs;
use std::path::PathBuf;
use std::process;

// Replace this with your library crate name if different.
use assembly_emulation::*; // <-- e.g. your lib with Cpu/Instructions/etc.

fn print_usage(prog: &str) {
    eprintln!(
        "Usage:\n  {prog} --in <input.bin> --out <memory.bin>\n\n\
         Options:\n  --in        Path to input file containing machine code bytes\n  \
                     --out       Path to write full memory image after execution\n"
    );
}

fn main() {
    // --- Parse args (simple/manual; no external deps) ---
    let mut args = env::args().skip(1); // skip program name
    let mut in_path: Option<PathBuf> = None;
    let mut out_path: Option<PathBuf> = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--in" => {
                let v = args.next();
                if v.is_none() {
                    eprintln!("--in requires a value");
                    print_usage(&env::args().next().unwrap_or_else(|| "program".into()));
                    process::exit(2);
                }
                in_path = Some(PathBuf::from(v.unwrap()));
            }
            "--out" => {
                let v = args.next();
                if v.is_none() {
                    eprintln!("--out requires a value");
                    print_usage(&env::args().next().unwrap_or_else(|| "program".into()));
                    process::exit(2);
                }
                out_path = Some(PathBuf::from(v.unwrap()));
            }
            "--help" | "-h" => {
                print_usage(&env::args().next().unwrap_or_else(|| "program".into()));
                return;
            }
            other => {
                eprintln!("Unknown argument: {other}");
                print_usage(&env::args().next().unwrap_or_else(|| "program".into()));
                process::exit(2);
            }
        }
    }

    let in_path = in_path.unwrap_or_else(|| {
        eprintln!("Missing --in");
        print_usage(&env::args().next().unwrap_or_else(|| "program".into()));
        process::exit(2);
    });

    let out_path = out_path.unwrap_or_else(|| {
        eprintln!("Missing --out");
        print_usage(&env::args().next().unwrap_or_else(|| "program".into()));
        process::exit(2);
    });

    let mut cpu = match Cpu::try_from_file(in_path.to_string_lossy().as_ref()) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Failed to read input file: {e}");
            process::exit(1);
        }
    };
    cpu.process_instructions();

    if let Err(e) = fs::write(&out_path, &cpu.memory) {
        eprintln!("Failed to write output memory file: {e}");
        process::exit(1);
    }
}

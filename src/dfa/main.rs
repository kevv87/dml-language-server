//  © 2024 Intel Corporation
//  SPDX-License-Identifier: Apache-2.0 and MIT
//! Utility to run DML Language Server directly on files
//!
//! Can be used for testing and obtaining understandable errors
//! rather than lsp messages

use std::path::PathBuf;
use std::io::Write;

use clap::{command, arg, Arg, ArgAction};

use log::debug;

pub fn main() {
    env_logger::init();
    let code = main_inner();
    std::process::exit(match code {
        Ok(()) => 0,
        Err(code) => code,
    });
}

#[derive(Debug)]
struct Args {
    binary: PathBuf,
    files: Vec<PathBuf>,
    workspaces: Vec<PathBuf>,
    compile_info: Option<PathBuf>,
    suppress_imports: Option<bool>,
    linting_enabled: Option<bool>,
    lint_cfg_path: Option<PathBuf>,
    test: bool,
    quiet: bool,
    autofix: bool,
    backup: bool,
}

fn parse_args() -> Args {
    let args = command!()
        .about(
            "A non-interactive frontend for the DLS. \
             DML files will be handled by the server as if \
             they were opened by user. And info about diagnostics \
             will be printed. Multiple devices _can_ be analyzed at \
             the same time.")
        .arg_required_else_help(true)
        .arg(arg!(<DLS> "The DLS binary to use")
             .value_parser(clap::value_parser!(PathBuf)))
        .arg_required_else_help(true)
        .arg(Arg::new("workspace").short('w').long("workspace")
             .help("Emulate a specific path as a workspace root")
             .action(ArgAction::Append)
             .value_parser(clap::value_parser!(PathBuf))
             .required(false))
        .arg(Arg::new("test").short('t')
             .help("If any diagnostic errors are reported, \
                    exit with errorcode")
             .action(ArgAction::Set)
             .value_parser(clap::value_parser!(bool))
            .required(false))
        .arg(Arg::new("quiet").short('q')
             .help("Do not output information about which errors \
                    were reported")
             .required(false))
        .arg(Arg::new("compile-info").short('c').long("compile-info")
             .help("Use the specified file to determine compilation flags and \
                    include paths")
             .action(ArgAction::Set)
             .value_parser(clap::value_parser!(PathBuf))
             .required(false))
        .arg(Arg::new("suppress-imports").short('s').long("suppress-imports")
            .help("Analyses specified files only, without also analyzing files they import")
            .action(ArgAction::Set)
            .value_parser(clap::value_parser!(bool))
            .required(false))
        .arg(Arg::new("linting-enabled").short('l').long("linting-enabled")
             .help("Turns linting on/off (defaults to true)")
             .action(ArgAction::Set)
             .value_parser(clap::value_parser!(bool))
             .required(false))
        .arg(Arg::new("lint-cfg-path").short('p').long("lint-cfg-path")
             .help("Parse the specified file as a linting configuration file")
             .action(ArgAction::Set)
             .value_parser(clap::value_parser!(PathBuf))
             .required(false))
        .arg(Arg::new("autofix")
             .long("autofix")
             .help("Automatically apply fixes for lint diagnostics")
             .action(ArgAction::SetTrue)
             .required(false))
        .arg(Arg::new("backup")
             .long("backup")
             .help("Create .bak backup files before applying autofixes")
             .action(ArgAction::SetTrue)
             .required(false))
        .arg(arg!(<PATH> ... "DML files to analyze")
             .value_parser(clap::value_parser!(PathBuf)))
        .arg_required_else_help(false)
        .get_matches();
    Args {
        binary: args.get_one::<PathBuf>("DLS")
            .expect("'DLS' is required").clone(),
        files: args.get_many("PATH")
            .expect("internal error. 'PATH' was None")
            .cloned().collect(),
        workspaces: args.get_many::<PathBuf>("workspace")
            .map_or(vec![], |vr|vr.cloned().collect()),
        quiet: args.contains_id("quiet"),
        test: args.get_one::<bool>("test").cloned().unwrap_or(false),
        compile_info: args.get_one::<PathBuf>("compile-info")
            .cloned(),
        suppress_imports: args.get_one::<bool>("suppress-imports")
            .cloned(),
        linting_enabled: args.get_one::<bool>("linting-enabled")
            .cloned(),
        lint_cfg_path: args.get_one::<PathBuf>("lint-cfg-path")
            .cloned(),
        autofix: args.get_flag("autofix"),
        backup: args.get_flag("backup"),
    }
}

fn main_inner() -> Result<(), i32> {
    let arg = parse_args();

    println!("DML direct file analysis ({})", env!("CARGO_PKG_VERSION"));
    debug!("DFA args are: {:?}", arg);

    if arg.backup && !arg.autofix {
        eprintln!("Warning: --backup flag is ignored without --autofix");
    }

    let request = dls::dfa::AnalysisRequest {
        files: arg.files.clone(),
        workspaces: arg.workspaces.clone(),
        linting_enabled: arg.linting_enabled.unwrap_or(true),
        suppress_imports: arg.suppress_imports.unwrap_or(false),
        compile_info: arg.compile_info.clone(),
        lint_cfg_path: arg.lint_cfg_path.clone(),
        autofix: arg.autofix,
        backup: arg.backup,
    };

    let result = dls::dfa::analyze_files(&arg.binary, request)
        .map_err(|e| {
            std::io::stdout().write_all(
                format!("Failed to analyze files: {}\n", e).as_bytes()
            ).ok();
            1
        })?;

    if !arg.quiet {
        for (file, diagnostics) in &result.diagnostics {
            println!("\n{}:", file.display());
            for diag in diagnostics {
                println!("  Line {}: {}", diag.line + 1, diag.message);
            }
        }
        
        if !result.fixes_applied.is_empty() {
            println!("\n✅ Fixes applied:");
            for (file, count) in &result.fixes_applied {
                println!("  {}: {} fix(es)", file.display(), count);
            }
        }
        
        if !result.fixes_skipped.is_empty() {
            println!("\n⚠️  Fixes skipped:");
            for (file, warnings) in &result.fixes_skipped {
                println!("  {}:", file.display());
                for warning in warnings {
                    println!("    {}", warning);
                }
            }
        }
    }

    if arg.test && result.has_errors {
        Err(1)
    } else {
        Ok(())
    }
}

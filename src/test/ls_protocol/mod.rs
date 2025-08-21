use jsonrpc::Response;
use lsp_types::notification::DidOpenTextDocument;
use lsp_types::request::Initialize;
use lsp_types::{DidOpenTextDocumentParams, InitializeResult, TextDocumentItem, Uri};
use serde_json;
use std::env;
use std::io;
use std::io::{Read, Write};
use std::marker::PhantomData;
use std::path::Path;
use std::process::{ChildStdout, Command, Stdio};
use std::str::FromStr;

use crate::file_management::CanonPath;
use crate::server::{Notification, Request, RequestId};

// Used to debug the child
#[allow(dead_code)]
fn wait_for_enter() {
    println!("Press Enter to continue...");
    io::stdout().flush().unwrap(); // Ensure the prompt is displayed
    let mut input = String::new();
    std::io::stdin()
        .read_line(&mut input)
        .expect("Failed to read line");
}

#[allow(dead_code)]
fn debug_child(child: &mut std::process::Child) {
    println!("Child PID: {}", child.id());
    wait_for_enter();
}

lazy_static::lazy_static! {
    static ref MOCK_URI: String = {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let abs_path = Path::new(manifest_dir).join("example_files/example.dml");
        CanonPath::from(abs_path.as_path())
            .as_str()
            .to_string()
    };
}

fn initialize_server(child: &mut std::process::Child) {
    let initialize_request = create_initialize_request();
    send_message(child, &add_header(&initialize_request));

    let server_res = get_one_msg_from_server(child);

    let _: InitializeResult = server_res
        .result()
        .ok()
        .expect("Did not find an init result as response!");
}

fn setup_test() -> std::process::Child {
    env::set_var("RUST_BACKTRACE", "1");
    env::set_var("RUST_LOG", "trace");

    let dls_bin = "target/debug/dls";
    let mut child = Command::new(dls_bin)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("Failed to start dls process");
    initialize_server(&mut child);
    child
}

fn send_message(child: &mut std::process::Child, message: &str) {
    if let Some(stdin) = child.stdin.as_mut() {
        stdin
            .write_all(message.as_bytes())
            .expect("Failed to write to stdin");
    } else {
        panic!("Child process does not have a stdin");
    }
}

fn teardown(child: &mut std::process::Child) {
    child.wait().expect("Failed while waiting child to join!");
}

fn server_buffer_to_json(msg_buffer: &str) -> Vec<&str> {
    let buffer_sections = msg_buffer.split("Content-Length:");
    let json_collection = buffer_sections
        .filter_map(|section| {
            let trimmed_section = section.trim();
            if trimmed_section.is_empty() || !trimmed_section.contains('{') {
                None
            } else {
                let json_start = trimmed_section.find('{').unwrap();
                let json_end = trimmed_section.rfind('}').unwrap() + 1;
                Some(&trimmed_section[json_start..json_end])
            }
        })
        .collect::<Vec<&str>>();
    json_collection
}

fn get_content_length(stdout: &mut ChildStdout) -> usize {
    let mut buffer = Vec::new();
    for byte in stdout.bytes() {
        let byte = byte.expect("Failed to read byte from stdout");
        buffer.push(byte);
        if byte == b'\r' {
            break;
        }
    }
    let content_length_str = String::from_utf8_lossy(&buffer);
    let content_length = content_length_str
        .split_whitespace()
        .nth(1)
        .expect("Failed to find content length")
        .parse::<usize>()
        .expect("Failed to parse content length");
    content_length + 3 // Taking into consideration the prepended \r\n\r
}

fn get_server_msg(child: &mut std::process::Child) -> String {
    let stdout = child
        .stdout
        .as_mut()
        .expect("Child process does not have a stdout. Unable to read server message.");
    let content_length = get_content_length(stdout);
    let mut buffer = vec![0; content_length];
    stdout
        .read_exact(&mut buffer)
        .expect("Failed to read the expected number of bytes from stdout");
    String::from_utf8_lossy(&buffer)
        .trim_end_matches('\0')
        .to_string()
}

fn add_header(mess: &str) -> String {
    format!("Content-Length: {}\r\n\r\n{}", mess.len(), mess)
}

static SOURCE: &str = "
dml 1.4;

bank sb_cr {
    group monitor {    

        register MKTME_KEYID_MASK {
            method get() -> (uint64) {
                local uint64 physical_address_mask = mse.srv10nm_mse_mktme.get_key_addr_mask();
                this.Mask.set(physical_address_mask);
                this.function_with_args('some_string',
                                integer,
                                floater);
                return this.val;
            }
        }

        register TDX_KEYID_MASK {
            method get() -> (uint64) {
                local uint64 tdx_keyid_mask = mse.srv10nm_mse_tdx.get_key_addr_mask();
                local uint64 some_uint = (is_this_real) ? then_you_might_like_this_value : or_this_one;
                this.Mask.set(tdx_keyid_mask);
                return this.val;
            }
        }
    }
}   

/*
    This is ONEEEE VEEEEEERY LLOOOOOOONG COOOMMMEENTT ON A SINGLEEEE LINEEEEEEEEEEEEEE
    and ANOTHEEEER VEEEEEERY LLOOOOOOONG COOOMMMEENTT ON A SINGLEEEE LINEEEEEEEEEEEEEE
*/

";

fn create_did_open_text_document_request(uri: &str, source: &str) -> String {
    let params = DidOpenTextDocumentParams {
        text_document: TextDocumentItem::new(
            Uri::from_str(uri).unwrap(),
            "dml".to_string(),
            0,
            source.to_string(),
        ),
    };
    Notification::<DidOpenTextDocument> {
        params,
        _action: PhantomData,
    }
    .to_string()
}

fn get_one_msg_from_server(child: &mut std::process::Child) -> Response {
    let output = get_server_msg(child);
    println!("Output: {}", output);
    let server_messages = server_buffer_to_json(&output);
    assert_eq!(
        server_messages.len(),
        1,
        "Expected one message in output, got: {:?}",
        server_messages
    );
    let jsonrpc_response: Response = serde_json::from_str(&server_messages[0].to_string())
        .expect("Failed to parse server output!");

    if jsonrpc_response.clone().check_error().is_err() {
        panic!("Got an error from the server response!");
    }
    jsonrpc_response
}

fn create_initialize_request() -> String {
    #[allow(deprecated)]
    let params = lsp_types::InitializeParams {
        process_id: None,
        root_path: None,
        root_uri: None,
        initialization_options: None,
        capabilities: lsp_types::ClientCapabilities::default(),
        trace: None,
        workspace_folders: None,
        client_info: None,
        locale: None,
        work_done_progress_params: lsp_types::WorkDoneProgressParams {
            work_done_token: None,
        },
    };
    let request = Request::<Initialize> {
        id: RequestId::from(serde_json::Value::from(123)),
        received: std::time::Instant::now(),
        params,
        _action: PhantomData,
    }
    .to_string();
    request
}

#[test]
pub fn test_01_initreq_responds_with_initres() {
    let mut child = setup_test();
    teardown(&mut child);
}

#[test]
pub fn test_02_did_open_responds_with_publish_diagnostics() {
    let mut child = setup_test();

    let req = create_did_open_text_document_request(&MOCK_URI, SOURCE);
    send_message(&mut child, &add_header(&req));

    let server_res = get_one_msg_from_server(&mut child);
    let diagnostics: lsp_types::PublishDiagnosticsParams = server_res
        .result()
        .ok()
        .expect("Couldnt parse server response as PublishDiagnostics");
    println!("\n{:?}", diagnostics);
    teardown(&mut child);
}

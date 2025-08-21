use std::marker::PhantomData;
use std::process::{ChildStdout, Command, Stdio};
use std::io::{Write, Read};
use std::env;
use std::str::FromStr;
use jsonrpc::Response;
use serde_json;
use lsp_types::{DidOpenTextDocumentParams, TextDocumentItem, Uri};
use lsp_types::notification::{DidOpenTextDocument};
use lsp_types::request::{Initialize};


use crate::server::{Notification, Request, RequestId};

fn setup_test() -> std::process::Child {
    env::set_var("RUST_BACKTRACE", "1");
    env::set_var("RUST_LOG", "debug");

    let dls_bin = "target/debug/dls";
    let child = Command::new(dls_bin)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("Failed to start dls process");
    child
}

fn send_message(child: &mut std::process::Child, message: &str) {
    if let Some(stdin) = child.stdin.as_mut() {
        println!("Sending:\n{}", message);
        stdin.write_all(message.as_bytes()).expect(
            "Failed to write to stdin");
    } else {
        panic!("Child process does not have a stdin");
    }
}

#[test]
pub fn test_01_empty_message_return_err() {
    let mut child = setup_test();
    send_message(&mut child, "");

    let exit_status = child.wait().expect(
        "Failed to wait for dls process");
    assert!(!exit_status.success(), 
        "DLS should return an error for empty message");
    let err_code = exit_status.code().unwrap();
    assert!(err_code == 101, "Expected 101 but got: {:?}", err_code);
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
    let stdout = child.stdout.as_mut().expect(
        "Child process does not have a stdout. Unable to read server message.");
    let content_length = get_content_length(stdout);
    let mut buffer = vec![0; content_length];
    stdout
        .read_exact(&mut buffer)
        .expect("Failed to read the expected number of bytes from stdout");
    String::from_utf8_lossy(&buffer)
        .trim_end_matches('\0')
        .to_string()
}

fn send_msg_and_wait(child: &mut std::process::Child, message: String) {
    send_message(child, message.as_str());
    // child.wait().expect("Failed to wait for dls process");
}

#[test]
pub fn test_02_empty_message_expect_err_on_stdout() {
    let mut child = setup_test();

    send_msg_and_wait(&mut child, "".to_string());
    
    let output = get_server_msg(&mut child);

    let server_messages = server_buffer_to_json(&output);
    assert_eq!(server_messages.len(), 1, 
        "Expected one message in output, got: {:?}", server_messages);
    let message = server_messages[0];
    let response: Response = serde_json::from_str(message)
        .expect("Failed to parse output as JSON");
    let response_err_code = response.error.unwrap().code;
    assert_eq!(response_err_code, -32700, 
        "Expected ParseError but got: {:?}", response_err_code);
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

fn create_did_open_text_document_request(
    uri: &str, source: &str) -> String
{
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
    }.to_string()
}

static MOCK_URI: &str = "file:///test.dml";

fn get_one_msg_from_server(child: &mut std::process::Child) -> String {
    let output = get_server_msg(child);
    println!("Output: {}", output);
    let server_messages = server_buffer_to_json(&output);
    assert_eq!(server_messages.len(), 1, 
        "Expected one message in output, got: {:?}", server_messages);
    server_messages[0].to_string()
}

#[test]
pub fn test_03_without_init_server_rejects() { 
    let mut child = setup_test();

    let did_open_notif = &create_did_open_text_document_request(MOCK_URI, SOURCE);

    send_msg_and_wait(&mut child, add_header(&did_open_notif));
    
    let message = get_one_msg_from_server(&mut child);
    let response: Response = serde_json::from_str(&message)
        .expect("Failed to parse output as JSON");
    let response_err_code = response.error.unwrap().code;
    assert_eq!(response_err_code, -32700, 
        "Expected ParseError but got: {:?}", response_err_code);
    
}

fn create_initialize_request() -> String {
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
    }.to_string();
    request
}

#[test]
pub fn test_04_initreq_responds_with_initres() {
    let mut child = setup_test();
    let initialize_request = create_initialize_request();
    send_msg_and_wait(&mut child, add_header(&initialize_request));

    // Print el mensaje en bytes
    let message = get_one_msg_from_server(&mut child);
    let response: Response = serde_json::from_str(&message)
        .expect("Failed to parse output as JSON");
    println!("Response: {:?}", response);

}

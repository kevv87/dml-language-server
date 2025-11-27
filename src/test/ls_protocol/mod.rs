use lsp_types::notification::{DidOpenTextDocument, Initialized, PublishDiagnostics};
use lsp_types::request::{CodeActionRequest, Initialize, Shutdown};
use lsp_types::{
    CodeActionContext, CodeActionParams, DidOpenTextDocumentParams, InitializeResult,
    PartialResultParams, Range, TextDocumentIdentifier, TextDocumentItem, Uri, WorkDoneProgressParams,
    CodeActionTriggerKind,
};
use serde::de::DeserializeOwned;
use serde::Serialize;
use serde_json::{self, Value};
use std::env;
use std::io::{BufRead, BufReader, Read, Write};
use std::marker::PhantomData;
use std::path::Path;
use std::process::{Child, ChildStdout, Command, Stdio};
use std::str::FromStr;

use crate::server::{Notification, Request, RequestId};

fn test_debug_enabled() -> bool {
    let enabled = env::var("DLS_TEST_DEBUG").is_ok();
    enabled
}

fn child_debug_enabled() -> bool {
    env::var("DLS_CHILD_DEBUG").is_ok()
}

struct LspClient {
    child: Child,
    reader: BufReader<ChildStdout>,
    request_id_counter: i64,
}

impl LspClient {
    fn new() -> Self {
        if child_debug_enabled() {
            env::set_var("RUST_BACKTRACE", "1");
            env::set_var("RUST_LOG", "debug");
        }

        let dls_bin = "target/debug/dls";
        let mut child = Command::new(dls_bin)
            .args(&["--linting", "true"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("Failed to start dls process");

        let stdout = child.stdout.take().expect("Failed to open stdout");
        let reader = BufReader::new(stdout);

        LspClient {
            child,
            reader,
            request_id_counter: 0,
        }
    }

    fn next_id(&mut self) -> RequestId {
        self.request_id_counter += 1;
        RequestId::from(Value::from(self.request_id_counter))
    }

    fn send_message(&mut self, message: &str) {
        let formatted_message = format!("Content-Length: {}\r\n\r\n{}", message.len(), message);
        let stdin = self.child.stdin.as_mut().expect("Failed to open stdin");
        stdin
            .write_all(formatted_message.as_bytes())
            .expect("Failed to write to stdin");
        stdin.flush().expect("Failed to flush stdin");
    }

    fn read_message(&mut self) -> String {
        let mut size = None;
        let mut buffer = String::new();

        loop {
            buffer.clear();
            if self.reader.read_line(&mut buffer).unwrap() == 0 {
                panic!("EOF while reading headers");
            }

            if buffer == "\r\n" {
                break;
            }

            let parts: Vec<&str> = buffer.splitn(2, ": ").collect();
            if parts.len() == 2 && parts[0] == "Content-Length" {
                size = Some(parts[1].trim().parse::<usize>().unwrap());
            }
        }

        let size = size.expect("Missing Content-Length header");
        let mut content = vec![0; size];
        self.reader.read_exact(&mut content).unwrap();

        String::from_utf8(content).expect("Invalid UTF-8 body")
    }

    fn send_request<R>(&mut self, params: R::Params) -> RequestId
    where
        R: lsp_types::request::Request,
        R::Params: Serialize,
    {
        let id = self.next_id();
        let request = Request::<R> {
            id: id.clone(),
            received: std::time::Instant::now(),
            params,
            _action: PhantomData,
        };
        self.send_message(&request.to_string());
        id
    }

    fn send_notification<N>(&mut self, params: N::Params)
    where
        N: lsp_types::notification::Notification,
        N::Params: Serialize,
    {
        let notification = Notification::<N> {
            params,
            _action: PhantomData,
        };
        self.send_message(&notification.to_string());
    }

    fn wait_for_response<R>(&mut self, id: RequestId) -> R
    where
        R: DeserializeOwned,
    {
        loop {
            let msg = self.read_message();
            let json_val: Value = serde_json::from_str(&msg).unwrap();

            if let Some(msg_id) = json_val.get("id") {
                let msg_id = RequestId::from(msg_id.clone());
                if msg_id == id {
                    if let Some(result) = json_val.get("result") {
                        return serde_json::from_value(result.clone()).unwrap();
                    } else if let Some(error) = json_val.get("error") {
                        panic!("Received error response: {:?}", error);
                    }
                }
            }
            // Ignore other messages (notifications, other requests)
        }
    }

    fn wait_for_notification<N>(&mut self) -> N::Params
    where
        N: lsp_types::notification::Notification,
        N::Params: DeserializeOwned,
    {
        loop {
            let msg = self.read_message();
            let json_val: Value = serde_json::from_str(&msg).unwrap();

            if let Some(method) = json_val.get("method") {
                if method == N::METHOD {
                    if let Some(params) = json_val.get("params") {
                        return serde_json::from_value(params.clone()).unwrap();
                    }
                }
            }
        }
    }
    
    fn initialize(&mut self) -> InitializeResult {
        let workspace_folders = Some(vec![lsp_types::WorkspaceFolder {
            uri: Uri::from_str(&MOCK_URI_WORKSPACE).unwrap(),
            name: "test_workspace".to_string(),
        }]);
        
        #[allow(deprecated)]
        let params = lsp_types::InitializeParams {
            process_id: None,
            root_path: None,
            root_uri: None,
            initialization_options: None,
            capabilities: lsp_types::ClientCapabilities::default(),
            trace: None,
            workspace_folders,
            client_info: None,
            locale: None,
            work_done_progress_params: lsp_types::WorkDoneProgressParams {
                work_done_token: None,
            },
        };

        let id = self.send_request::<Initialize>(params);
        self.wait_for_response::<InitializeResult>(id)
    }

    fn shutdown(&mut self) {
         let id = self.send_request::<Shutdown>(());
         self.wait_for_response::<()>(id);
    }

    fn exit(&mut self) {
        self.send_notification::<lsp_types::notification::Exit>(());
    }
}

impl Drop for LspClient {
    fn drop(&mut self) {
        // Try to kill if still running, though we should exit gracefully in tests
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

lazy_static::lazy_static! {
    static ref MOCK_URI: String = {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let abs_path = Path::new(manifest_dir).join("example_files/example.dml");
        let uri_string = format!("file://{}", abs_path.display());
        uri_string
    };
    static ref MOCK_URI_WORKSPACE: String = {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let abs_path = Path::new(manifest_dir);
        let uri_string = format!("file://{}", abs_path.display());
        uri_string
    };
    static ref MOCK_URI_AUTOFIX: String = {
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let abs_path = Path::new(manifest_dir).join("example_files/autofix.dml");
        let uri_string = format!("file://{}", abs_path.display());
        uri_string
    };
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
";

static SOURCE_AUTOFIX: &str = "
dml 1.4;

method this_is_some_method() {return 0;}
";

#[test]
fn test_lifecycle_basic() {
    let mut client = LspClient::new();
    
    // Initialize
    // This implicitly asserts that the server responds with a valid InitializeResult.
    // If the server returns an error or invalid JSON, wait_for_response will panic.
    let _init_result = client.initialize();
    
    // Initialized
    client.send_notification::<Initialized>(lsp_types::InitializedParams {});
    
    // Shutdown
    client.shutdown();
    
    // Exit
    client.exit();
}

#[test]
fn test_did_open_diagnostics() {
    let mut client = LspClient::new();
    client.initialize();
    client.send_notification::<Initialized>(lsp_types::InitializedParams {});

    let params = DidOpenTextDocumentParams {
        text_document: TextDocumentItem::new(
            Uri::from_str(&MOCK_URI).unwrap(),
            "dml".to_string(),
            0,
            SOURCE.to_string(),
        ),
    };
    client.send_notification::<DidOpenTextDocument>(params);

    let mut diagnostics_params = client.wait_for_notification::<PublishDiagnostics>();
    let mut retries = 10;
    while diagnostics_params.diagnostics.is_empty() && retries > 0 {
        diagnostics_params = client.wait_for_notification::<PublishDiagnostics>();
        retries -= 1;
    }
    if test_debug_enabled() {
        println!("Received Diagnostics: {:?}", diagnostics_params.diagnostics);
    }
    
    assert!(!diagnostics_params.diagnostics.is_empty(), "Expected at least one diagnostic, got none after retries");
    
    client.shutdown();
    client.exit();
}

#[test]
fn test_code_action() {
    let mut client = LspClient::new();
    client.initialize();
    client.send_notification::<Initialized>(lsp_types::InitializedParams {});

    let uri = Uri::from_str(&MOCK_URI).unwrap();
    let params = DidOpenTextDocumentParams {
        text_document: TextDocumentItem::new(
            uri.clone(),
            "dml".to_string(),
            0,
            SOURCE.to_string(),
        ),
    };
    client.send_notification::<DidOpenTextDocument>(params);

    let mut diagnostics_params = client.wait_for_notification::<PublishDiagnostics>();
    let mut retries = 10;
    while diagnostics_params.diagnostics.is_empty() && retries > 0 {
        diagnostics_params = client.wait_for_notification::<PublishDiagnostics>();
        retries -= 1;
    }
    if test_debug_enabled() {
        println!("Diagnostics before CodeAction: {:?}", diagnostics_params.diagnostics);
    }

    let code_action_params = CodeActionParams {
        text_document: TextDocumentIdentifier { uri },
        range: Range {
            start: lsp_types::Position { line: 5, character: 0 },
            end: lsp_types::Position { line: 6, character: 0 },
        },
        context: CodeActionContext {
            diagnostics: vec![],
            only: None,
            trigger_kind: Some(CodeActionTriggerKind::INVOKED),
        },
        work_done_progress_params: WorkDoneProgressParams {
            work_done_token: None,
        },
        partial_result_params: PartialResultParams {
            partial_result_token: None,
        },
    };

    let id = client.send_request::<CodeActionRequest>(code_action_params);
    
    let response: Option<Vec<lsp_types::CodeActionOrCommand>> = client.wait_for_response(id);
    
    if test_debug_enabled() {
        println!("CodeAction response: {:?}", response);
    }
    
    // Assert server responds with Some (supports CodeActions) but empty (no actions yet)
    assert!(response.is_some(), "Server should support CodeActions");
    assert!(response.unwrap().is_empty(), "No code actions implemented yet");

    client.shutdown();
    client.exit();
}

#[test]
fn test_diagnostic_has_autofix_data() {
    let mut client = LspClient::new();
    client.initialize();
    client.send_notification::<Initialized>(lsp_types::InitializedParams {});

    let params = DidOpenTextDocumentParams {
        text_document: TextDocumentItem::new(
            Uri::from_str(&MOCK_URI_AUTOFIX).unwrap(),
            "dml".to_string(),
            0,
            SOURCE_AUTOFIX.to_string(),
        ),
    };
    client.send_notification::<DidOpenTextDocument>(params);

    let mut diagnostics_params = client.wait_for_notification::<PublishDiagnostics>();
    let mut retries = 10;
    while diagnostics_params.diagnostics.is_empty() && retries > 0 {
        diagnostics_params = client.wait_for_notification::<PublishDiagnostics>();
        retries -= 1;
    }
    
    if test_debug_enabled() {
        println!("Received Diagnostics: {:?}", diagnostics_params.diagnostics);
    }

    assert!(!diagnostics_params.diagnostics.is_empty(), "Expected diagnostics with autofix");
    
    let has_data = diagnostics_params.diagnostics.iter()
        .any(|d| d.data.is_some());
    
    assert!(has_data, "Expected at least one diagnostic with data field containing fix");

    client.shutdown();
    client.exit();
}

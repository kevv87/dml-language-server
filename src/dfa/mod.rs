//  © 2024 Intel Corporation
//  SPDX-License-Identifier: Apache-2.0 and MIT
pub mod client;

#[cfg(test)]
mod test;

pub(crate) mod text_edit;

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use anyhow::{anyhow, Result};
use crate::config::Config;
use subprocess::ExitStatus;

pub use client::ClientInterface;

pub struct AnalysisRequest {
    pub files: Vec<PathBuf>,
    pub workspaces: Vec<PathBuf>,
    pub linting_enabled: bool,
    pub suppress_imports: bool,
    pub compile_info: Option<PathBuf>,
    pub lint_cfg_path: Option<PathBuf>,
    pub autofix: bool,
}

impl Default for AnalysisRequest {
    fn default() -> Self {
        Self {
            files: vec![],
            workspaces: vec![],
            linting_enabled: true,
            suppress_imports: false,
            compile_info: None,
            lint_cfg_path: None,
            autofix: false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct DiagnosticSummary {
    pub line: u32,
    pub message: String,
}

pub struct AnalysisResult {
    pub files_analyzed: usize,
    pub has_errors: bool,
    pub diagnostics: HashMap<PathBuf, Vec<DiagnosticSummary>>,
    pub fixes_applied: HashMap<PathBuf, usize>,
    pub fixes_skipped: HashMap<PathBuf, Vec<String>>,
}

pub fn analyze_files(
    dls_binary: &Path,
    request: AnalysisRequest
) -> Result<AnalysisResult> {
    let mut client = setup_client(dls_binary, &request)?;
    
    open_and_analyze_files(&mut client, &request.files)?;
    
    let mut result = collect_diagnostics(&client, &request.files);
    
    if request.autofix {
        apply_fixes_to_files(&mut client, &request.files, &mut result)?;
    }
    
    client.shutdown().ok();
    
    Ok(result)
}

fn setup_client(
    dls_binary: &Path,
    request: &AnalysisRequest
) -> Result<ClientInterface> {
    let root = if !request.workspaces.is_empty() {
        &request.workspaces[0]
    } else if !request.files.is_empty() {
        request.files.iter()
            .filter_map(|p| p.parent())
            .reduce(|a, n| if a.starts_with(n) { a } else { n })
            .ok_or_else(|| anyhow!("Could not determine workspace root"))?
    } else {
        return Err(anyhow!("No files or workspaces provided"));
    };
    
    let mut client = ClientInterface::start(dls_binary, root, request.linting_enabled)?;
    
    if request.workspaces.len() > 1 {
        client.add_workspaces(request.workspaces[1..].to_vec())?;
    }
    
    let config = Config {
        compile_info_path: request.compile_info.clone(),
        suppress_imports: request.suppress_imports,
        linting_enabled: request.linting_enabled,
        lint_cfg_path: request.lint_cfg_path.clone(),
        ..Default::default()
    };
    client.set_config(config)?;
    
    Ok(client)
}

fn open_and_analyze_files(
    client: &mut ClientInterface,
    files: &[PathBuf]
) -> Result<()> {
    for file in files {
        client.open_file(file)?;
    }
    
    if !files.is_empty() {
        client.wait_for_analysis().map_err(|e| match e {
            ExitStatus::Exited(u) => anyhow!("Process exited with code: {}", u),
            ExitStatus::Signaled(u) => anyhow!("Process signaled: {}", u),
            ExitStatus::Other(i) => anyhow!("Process exit status: {}", i),
            ExitStatus::Undetermined => anyhow!("Process exit status undetermined"),
        })?;
    }
    
    Ok(())
}

fn collect_diagnostics(
    client: &ClientInterface,
    files: &[PathBuf]
) -> AnalysisResult {
    let has_errors = !client.no_errors();
    
    let mut diagnostics = HashMap::new();
    
    for file in files {
        if let Some(file_diagnostics) = client.get_diagnostics(file) {
            let summaries: Vec<DiagnosticSummary> = file_diagnostics
                .iter()
                .map(|d| DiagnosticSummary {
                    line: d.range.start.line,
                    message: d.message.clone(),
                })
                .collect();
            
            if !summaries.is_empty() {
                diagnostics.insert(file.clone(), summaries);
            }
        }
    }
    
    AnalysisResult {
        files_analyzed: files.len(),
        has_errors,
        diagnostics,
        fixes_applied: HashMap::new(),
        fixes_skipped: HashMap::new(),
    }
}

fn apply_fixes_to_files(
    client: &mut ClientInterface,
    files: &[PathBuf],
    result: &mut AnalysisResult,
) -> Result<()> {
    for file in files {
        let diagnostics_with_fixes = get_diagnostics_with_fixes(client, file);
        
        if diagnostics_with_fixes.is_empty() {
            continue;
        }
        
        let code_actions = request_code_actions_for_file(client, file, diagnostics_with_fixes)?;
        
        if code_actions.is_empty() {
            continue;
        }
        
        let edits = extract_text_edits_from_actions(code_actions);
        
        if edits.is_empty() {
            continue;
        }
        
        if text_edit::has_conflicting_edits(&edits) {
            record_skipped_fix(result, file, "conflicting edits detected");
            continue;
        }
        
        apply_edits_to_file(file, &edits)?;
        result.fixes_applied.insert(file.clone(), edits.len());
    }
    
    Ok(())
}

fn get_diagnostics_with_fixes(
    client: &ClientInterface,
    file: &Path
) -> Vec<lsp_types::Diagnostic> {
    client
        .get_diagnostics(file)
        .map(|diags| {
            diags
                .iter()
                .filter(|d| d.data.is_some())
                .cloned()
                .collect()
        })
        .unwrap_or_default()
}

fn request_code_actions_for_file(
    client: &mut ClientInterface,
    file: &Path,
    diagnostics: Vec<lsp_types::Diagnostic>
) -> Result<Vec<lsp_types::CodeAction>> {
    use lsp_types::{Position, Range};
    use crate::lsp_data::parse_uri;
    
    let canon_path = crate::file_management::CanonPath::from(file);
    let uri = parse_uri(canon_path.to_str().unwrap())
        .map_err(|e| anyhow!("Invalid file path: {}", e))?;
    
    let file_range = Range {
        start: Position { line: 0, character: 0 },
        end: Position { line: u32::MAX, character: 0 },
    };
    
    client.request_code_actions(uri, file_range, diagnostics)
}

fn extract_text_edits_from_actions(
    actions: Vec<lsp_types::CodeAction>
) -> Vec<lsp_types::TextEdit> {
    let mut edits = Vec::new();
    
    for action in actions {
        if let Some(workspace_edit) = action.edit {
            if let Some(changes) = workspace_edit.changes {
                for (_, text_edits) in changes {
                    edits.extend(text_edits);
                }
            }
        }
    }
    
    edits
}

fn record_skipped_fix(result: &mut AnalysisResult, file: &Path, reason: &str) {
    let warning = format!(
        "Skipping fixes for {}: {}",
        file.display(),
        reason
    );
    eprintln!("⚠️  {}", warning);
    result.fixes_skipped
        .entry(file.to_path_buf())
        .or_insert_with(Vec::new)
        .push(warning);
}

fn apply_edits_to_file(file: &Path, edits: &[lsp_types::TextEdit]) -> Result<()> {
    let content = std::fs::read_to_string(file)?;
    let new_content = text_edit::apply_edits_to_content(&content, edits)?;
    std::fs::write(file, new_content)?;
    Ok(())
}


//  © 2024 Intel Corporation
//  SPDX-License-Identifier: Apache-2.0 and MIT
pub mod client;

#[cfg(test)]
mod test;

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use anyhow::{anyhow, Result};
use client::ClientInterface;
use crate::config::Config;
use subprocess::ExitStatus;

pub struct AnalysisRequest {
    pub files: Vec<PathBuf>,
    pub workspaces: Vec<PathBuf>,
    pub linting_enabled: bool,
    pub suppress_imports: bool,
    pub compile_info: Option<PathBuf>,
    pub lint_cfg_path: Option<PathBuf>,
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
}

pub fn analyze_files(
    dls_binary: &Path,
    request: AnalysisRequest
) -> Result<AnalysisResult> {
    let mut client = setup_client(dls_binary, &request)?;
    
    open_and_analyze_files(&mut client, &request.files)?;
    
    let result = collect_diagnostics(&client, &request.files);
    
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
    
    let diagnostics = HashMap::new();
    
    AnalysisResult {
        files_analyzed: files.len(),
        has_errors,
        diagnostics,
    }
}


#[cfg(test)]
mod tests {
    use crate::dfa::{analyze_files, AnalysisRequest};
    use std::fs;
    use std::path::Path;
    use tempfile::TempDir;

    #[test]
    fn test_dfa_analyze_files() {
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let test_file = temp_dir.path().join("test.dml");
        
        fs::write(&test_file, 
            "dml 1.4;\n\nmethod this_is_some_method() {return 0;}\n"
        ).expect("Failed to write test file");
        
        let dls_binary = Path::new("target/debug/dls");
        
        let request = AnalysisRequest {
            files: vec![test_file],
            workspaces: vec![temp_dir.path().to_path_buf()],
            linting_enabled: true,
            suppress_imports: true,
            ..Default::default()
        };
        
        let result = analyze_files(dls_binary, request)
            .expect("Analysis should succeed");
        
        assert_eq!(result.files_analyzed, 1);
        assert!(result.has_errors, "Expected to find linting errors in test file");
    }
}

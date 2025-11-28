#[cfg(test)]
mod tests {
    use crate::dfa::{analyze_files, AnalysisRequest};
    use std::fs;
    use std::path::Path;
    use tempfile::TempDir;

    #[test]
    fn test_dfa_analyze_files() {
        let source_code = "dml 1.4;\n\nmethod this_is_some_method() {return 0;}\n";
        
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let test_file = temp_dir.path().join("test.dml");
        
        fs::write(&test_file, source_code).expect("Failed to write test file");
        
        let dls_binary = Path::new("target/debug/dls");
        
        let request = AnalysisRequest {
            files: vec![test_file.clone()],
            workspaces: vec![temp_dir.path().to_path_buf()],
            linting_enabled: true,
            suppress_imports: true,
            ..Default::default()
        };
        
        let result = analyze_files(dls_binary, request)
            .expect("Analysis should succeed");
        
        assert_eq!(result.files_analyzed, 1);
        assert!(result.has_errors, "Expected to find linting errors in test file");
        
        assert!(!result.diagnostics.is_empty(), 
            "Expected diagnostics to be populated");
        
        let file_diagnostics = result.diagnostics.get(&test_file)
            .expect("Expected diagnostics for test file");
        assert!(!file_diagnostics.is_empty(), 
            "Expected at least one diagnostic");
    }

    #[test]
    fn test_dfa_analyze_files_with_autofix() {
        let source_code = "dml 1.4;\n\nmethod foo() {return 0;}\n";
        let expected_fixed = "dml 1.4;\n\nmethod foo() { return 0; }\n";
        
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let test_file = temp_dir.path().join("test.dml");
        
        fs::write(&test_file, source_code).expect("Failed to write test file");
        
        let dls_binary = Path::new("target/debug/dls");
        
        let request = AnalysisRequest {
            files: vec![test_file.clone()],
            workspaces: vec![temp_dir.path().to_path_buf()],
            linting_enabled: true,
            suppress_imports: true,
            autofix: true,
            ..Default::default()
        };
        
        let result = analyze_files(dls_binary, request)
            .expect("Analysis with autofix should succeed");
        
        assert_eq!(result.files_analyzed, 1);
        
        assert!(!result.diagnostics.is_empty(), 
            "Expected diagnostics to be populated even with autofix");
        
        if let Some(fixes_count) = result.fixes_applied.get(&test_file) {
            assert!(*fixes_count > 0, "Expected at least one fix to be applied");
            
            let content = fs::read_to_string(&test_file).unwrap();
            assert_eq!(content, expected_fixed, 
                "Expected file to contain fixed spacing");
        }
    }

    #[test]
    fn test_dfa_analyze_files_without_linting() {
        let source_code = "dml 1.4;\n\nmethod foo() { return 0; }\n";
        
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let test_file = temp_dir.path().join("test.dml");
        
        fs::write(&test_file, source_code).expect("Failed to write test file");
        
        let dls_binary = Path::new("target/debug/dls");
        
        let request = AnalysisRequest {
            files: vec![test_file.clone()],
            workspaces: vec![temp_dir.path().to_path_buf()],
            linting_enabled: false,
            suppress_imports: true,
            autofix: false,
            ..Default::default()
        };
        
        let result = analyze_files(dls_binary, request)
            .expect("Analysis should succeed");
        
        assert_eq!(result.files_analyzed, 1);
        
        let lint_diagnostics = result.diagnostics.get(&test_file)
            .map(|diags| diags.iter().filter(|d| d.message.contains("spacing") || d.message.contains("brace")).count())
            .unwrap_or(0);
        
        assert_eq!(lint_diagnostics, 0, 
            "Expected no lint-specific diagnostics when linting disabled");
    }

    #[test]
    fn test_dfa_autofix_with_backup() {
        let source_code = "dml 1.4;\n\nmethod foo() {return 0;}\n";
        let expected_fixed = "dml 1.4;\n\nmethod foo() { return 0; }\n";
        
        let temp_dir = TempDir::new().expect("Failed to create temp dir");
        let test_file = temp_dir.path().join("test.dml");
        
        fs::write(&test_file, source_code).expect("Failed to write test file");
        
        let dls_binary = Path::new("target/debug/dls");
        
        let request = AnalysisRequest {
            files: vec![test_file.clone()],
            workspaces: vec![temp_dir.path().to_path_buf()],
            linting_enabled: true,
            suppress_imports: true,
            autofix: true,
            backup: true,
            ..Default::default()
        };
        
        let result = analyze_files(dls_binary, request)
            .expect("Analysis should succeed");
        
        assert_eq!(result.files_analyzed, 1);
        assert!(!result.fixes_applied.is_empty(), "Expected fixes to be applied");
        
        let backup_file = test_file.with_extension("dml.bak");
        assert!(backup_file.exists(), "Backup file should exist");
        
        let backup_content = fs::read_to_string(&backup_file)
            .expect("Should read backup file");
        assert_eq!(backup_content, source_code, "Backup should contain original content");
        
        let fixed_content = fs::read_to_string(&test_file)
            .expect("Should read fixed file");
        assert!(fixed_content.contains(expected_fixed), 
            "File should be fixed. Got: {}", fixed_content);
    }
}

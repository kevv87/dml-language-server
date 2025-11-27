//  © 2024 Intel Corporation
//  SPDX-License-Identifier: Apache-2.0 and MIT

use lsp_types::{Position, Range, TextEdit};
use anyhow::{anyhow, Result};

pub(crate) fn apply_edit_to_content(content: &str, edit: &TextEdit) -> Result<String> {
    let mut line_start_positions = vec![0];
    for (i, ch) in content.char_indices() {
        if ch == '\n' {
            line_start_positions.push(i + 1);
        }
    }
    
    let start_line = edit.range.start.line as usize;
    let start_char = edit.range.start.character as usize;
    let end_line = edit.range.end.line as usize;
    let end_char = edit.range.end.character as usize;
    
    if start_line >= line_start_positions.len() {
        return Err(anyhow!("Edit start line {} out of bounds", start_line));
    }
    
    let start_byte_offset = line_start_positions[start_line] + start_char;
    
    let end_byte_offset = if end_line < line_start_positions.len() {
        line_start_positions[end_line] + end_char
    } else {
        content.len()
    };
    
    if start_byte_offset > content.len() || end_byte_offset > content.len() {
        return Err(anyhow!("Edit positions out of bounds"));
    }
    
    let mut result = String::new();
    result.push_str(&content[..start_byte_offset]);
    result.push_str(&edit.new_text);
    result.push_str(&content[end_byte_offset..]);
    
    Ok(result)
}

pub(crate) fn apply_edits_to_content(content: &str, edits: &[TextEdit]) -> Result<String> {
    if edits.is_empty() {
        return Ok(content.to_string());
    }
    
    let mut sorted_edits = edits.to_vec();
    sorted_edits.sort_by(|a, b| {
        b.range.start.line.cmp(&a.range.start.line)
            .then(b.range.start.character.cmp(&a.range.start.character))
    });
    
    let mut result = content.to_string();
    
    for edit in sorted_edits.iter() {
        result = apply_edit_to_content(&result, edit)?;
    }
    
    Ok(result)
}

fn ranges_overlap(r1: &Range, r2: &Range) -> bool {
    !(r1.end.line < r2.start.line || 
      (r1.end.line == r2.start.line && r1.end.character <= r2.start.character) ||
      r2.end.line < r1.start.line ||
      (r2.end.line == r1.start.line && r2.end.character <= r1.start.character))
}

pub(crate) fn has_conflicting_edits(edits: &[TextEdit]) -> bool {
    for i in 0..edits.len() {
        for j in (i + 1)..edits.len() {
            if ranges_overlap(&edits[i].range, &edits[j].range) {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_apply_single_edit_insertion() {
        let content = "method foo() {return 0;}";
        let edit = TextEdit {
            range: Range {
                start: Position { line: 0, character: 13 },
                end: Position { line: 0, character: 13 },
            },
            new_text: " ".to_string(),
        };
        
        let result = apply_edit_to_content(content, &edit).unwrap();
        assert_eq!(result, "method foo()  {return 0;}");
    }

    #[test]
    fn test_apply_multiple_edits() {
        let content = "method foo() {return 0;}";
        let edits = vec![
            TextEdit {
                range: Range {
                    start: Position { line: 0, character: 13 },
                    end: Position { line: 0, character: 13 },
                },
                new_text: " ".to_string(),
            },
            TextEdit {
                range: Range {
                    start: Position { line: 0, character: 23 },
                    end: Position { line: 0, character: 23 },
                },
                new_text: " ".to_string(),
            },
        ];
        
        let result = apply_edits_to_content(content, &edits).unwrap();
        assert_eq!(result, "method foo()  {return 0; }");
    }

    #[test]
    fn test_detect_overlapping_edits() {
        let edit1 = TextEdit {
            range: Range {
                start: Position { line: 0, character: 5 },
                end: Position { line: 0, character: 10 },
            },
            new_text: "test".to_string(),
        };
        let edit2 = TextEdit {
            range: Range {
                start: Position { line: 0, character: 8 },
                end: Position { line: 0, character: 12 },
            },
            new_text: "conflict".to_string(),
        };
        
        assert!(has_conflicting_edits(&[edit1, edit2]));
    }

    #[test]
    fn test_non_overlapping_edits() {
        let edit1 = TextEdit {
            range: Range {
                start: Position { line: 0, character: 5 },
                end: Position { line: 0, character: 10 },
            },
            new_text: "test".to_string(),
        };
        let edit2 = TextEdit {
            range: Range {
                start: Position { line: 0, character: 15 },
                end: Position { line: 0, character: 20 },
            },
            new_text: "other".to_string(),
        };
        
        assert!(!has_conflicting_edits(&[edit1, edit2]));
    }
}

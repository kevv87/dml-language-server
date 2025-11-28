//  © 2024 Intel Corporation
//  SPDX-License-Identifier: Apache-2.0 and MIT

use ropey::Rope;
use lsp_types::{Position, Range, TextEdit};
use anyhow::{anyhow, Result};
use std::path::Path;

struct TextBuffer {
    rope: Rope,
}

impl TextBuffer {
    fn from_str(content: &str) -> Result<Self> {
        let rope = Rope::from_str(content);
        Ok(Self { rope })
    }

    fn apply_edit(&mut self, edit: &TextEdit) -> Result<()> {
        let start_idx = self.position_to_char(edit.range.start)?;
        let end_idx = self.position_to_char(edit.range.end)?;

        if start_idx > end_idx {
            return Err(anyhow!("Invalid edit range: start > end"));
        }

        self.rope.remove(start_idx..end_idx);
        self.rope.insert(start_idx, &edit.new_text);
        Ok(())
    }

    fn apply_edits(&mut self, edits: &[TextEdit]) -> Result<()> {
        let mut sorted = edits.to_vec();
        sorted.sort_by(|a, b| {
            b.range.start.line
                .cmp(&a.range.start.line)
                .then_with(|| b.range.start.character.cmp(&a.range.start.character))
        });

        for edit in sorted {
            self.apply_edit(&edit)?;
        }
        Ok(())
    }

    fn position_to_char(&self, pos: Position) -> Result<usize> {
        let line_idx = pos.line as usize;
        
        if line_idx >= self.rope.len_lines() {
            return Err(anyhow!(
                "Line {} out of bounds (max: {})",
                line_idx,
                self.rope.len_lines()
            ));
        }

        let line_start = self.rope.line_to_char(line_idx);
        let char_offset = pos.character as usize;

        Ok(line_start + char_offset)
    }

    fn write_to_file(&self, path: &Path) -> Result<()> {
        let mut file = std::fs::File::create(path)?;
        self.rope.write_to(&mut file)?;
        Ok(())
    }
}

pub(crate) fn apply_edits_to_content(content: &str, path: &Path, edits: &[TextEdit]) -> Result<()> {
    let mut buffer = TextBuffer::from_str(content)?;
    buffer.apply_edits(edits)?;
    buffer.write_to_file(path)?;
    Ok(())
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

//  © 2024 Intel Corporation
//  SPDX-License-Identifier: Apache-2.0 and MIT
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::server::{Notification, Output};
use lazy_static::lazy_static;
use lsp_types::notification::{Progress, PublishDiagnostics, ShowMessage};
use lsp_types::{MessageType,
                ProgressParams, ProgressParamsValue, ProgressToken,
                PublishDiagnosticsParams, ShowMessageParams,
                WorkDoneProgress,
                WorkDoneProgressBegin,
                WorkDoneProgressReport,
                WorkDoneProgressEnd};


/// Communication of build progress back to the client.
pub trait ProgressNotifier {
    fn id(&self) -> String;
    fn notify_begin_progress(&self);
    fn update(&mut self, update: ProgressUpdate);
    fn notify_progress(&mut self, update: ProgressUpdate);
    fn notify_end_progress(&self);
}

/// Kinds of progress updates.
pub enum ProgressUpdate {
    Message(String),
    Percentage(u32),
    Cancellable(bool),
}

/// Trait for communication of diagnostics (i.e., analysis results)
/// back to the rest of the DLS (and on to the client).
// This trait only really exists to work around the object safety rules (Output
// is not object-safe).
pub trait DiagnosticsNotifier {
    fn id(&self) -> String;
    fn notify_begin_diagnostics(&self);
    fn update(&mut self, update: ProgressUpdate);
    fn notify_progress(&mut self, update: ProgressUpdate);
    fn notify_publish_diagnostics(&self, _: PublishDiagnosticsParams);
    fn notify_error_diagnostics(&self, msg: String);
    fn notify_end_diagnostics(&self);
}

/// Notifier of progress for the analysis (window/progress notifications).
/// the same instance is used for the entirety of one single build.
pub struct AnalysisProgressNotifier<O: Output> {
    out: O,
    id: String,
    title: String,
    cancellable: bool,
    message: Option<String>,
    percentage: Option<u32>,
}

impl<O: Output> AnalysisProgressNotifier<O> {
    pub fn new_with_id(id: String, title: String, out: O)
                       -> AnalysisProgressNotifier<O> {
        AnalysisProgressNotifier {
            out,
            id ,
            title,
            cancellable: false,
            message: None,
            percentage: None,
        }
    }
    pub fn new(title: String, out: O) -> AnalysisProgressNotifier<O> {
        // Counter to generate unique IDs for each chain-of-progress
        // notification.
        lazy_static! {
            static ref PROGRESS_ID_COUNTER: AtomicUsize = AtomicUsize::new(0);
        };
        Self::new_with_id(
            format!("progress_{}",
                    PROGRESS_ID_COUNTER.fetch_add(1, Ordering::SeqCst)),
            title, out)
    }

    fn begin_params(&self) -> ProgressParams {
        ProgressParams {
            token: ProgressToken::String(self.id.clone()),
            value: ProgressParamsValue::WorkDone(
                WorkDoneProgress::Begin(
                    WorkDoneProgressBegin {
                        title: self.title.clone(),
                        cancellable: Some(self.cancellable),
                        message: self.message.clone(),
                        percentage: self.percentage,
                    })
            ),
        }
    }

    fn progress_params(&self) -> ProgressParams {
        ProgressParams {
            token: ProgressToken::String(self.id.clone()),
            value: ProgressParamsValue::WorkDone(
                WorkDoneProgress::Report(
                    WorkDoneProgressReport {
                        cancellable: Some(self.cancellable),
                        message: self.message.clone(),
                        percentage: self.percentage,
                    })
            ),
        }
    }

    fn end_params(&self) -> ProgressParams {
        ProgressParams {
            token: ProgressToken::String(self.id.clone()),
            value: ProgressParamsValue::WorkDone(
                WorkDoneProgress::End(
                    WorkDoneProgressEnd {
                        message: self.message.clone(),
                    })
            ),
        }
    }
}

impl<O: Output> ProgressNotifier for AnalysisProgressNotifier<O> {
    fn id(&self) -> String {
        self.id.clone()
    }
    fn update(&mut self, update: ProgressUpdate) {
        match update {
            ProgressUpdate::Message(s) => self.message = Some(s),
            // TODO: We could sanity check that percentage remains
            // non-decreasing here
            ProgressUpdate::Percentage(p) => self.percentage = Some(p),
            ProgressUpdate::Cancellable(b) => self.cancellable = b,
        }
    }
    fn notify_begin_progress(&self) {
        self.out.notify(Notification::<Progress>::new(self.begin_params()));
    }
    fn notify_progress(&mut self, update: ProgressUpdate) {
        self.update(update);
        self.out.notify(Notification::<Progress>::new(self.progress_params()));
    }
    fn notify_end_progress(&self) {
        self.out.notify(Notification::<Progress>::new(self.end_params()));
    }
}

/// Notifier of diagnostics after analysis has completed
pub struct AnalysisDiagnosticsNotifier<O: Output> {
    sub_notifier: AnalysisProgressNotifier<O>,
}

impl <O: Output> AnalysisDiagnosticsNotifier<O> {
    pub fn new(title: String, out: O) -> AnalysisDiagnosticsNotifier<O> {
        AnalysisDiagnosticsNotifier {
            sub_notifier: AnalysisProgressNotifier::new(title, out),
        }
    }
}

impl <O: Output> DiagnosticsNotifier for AnalysisDiagnosticsNotifier<O> {
    fn id(&self) -> String {
        self.sub_notifier.id()
    }
    fn notify_begin_diagnostics(&self) {
        self.sub_notifier.notify_begin_progress();
    }
    fn notify_publish_diagnostics(&self, params: PublishDiagnosticsParams) {
        self.sub_notifier.out.notify(
            Notification::<PublishDiagnostics>::new(params));
    }
    fn notify_error_diagnostics(&self, message: String) {
        self.sub_notifier.out.notify(
            Notification::<ShowMessage>::new(ShowMessageParams {
                typ: MessageType::ERROR,
                message,
        }));
    }
    fn update(&mut self, update: ProgressUpdate) {
        self.sub_notifier.update(update);
    }
    fn notify_progress(&mut self, update: ProgressUpdate) {
        self.sub_notifier.notify_progress(update);
    }
    fn notify_end_diagnostics(&self) {
        self.sub_notifier.notify_end_progress();
    }
}

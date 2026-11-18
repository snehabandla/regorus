// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Minimal helpers for catching panics inside the FFI layer.
//!
//! These are not yet wired into the exported functions; they will
//! be used once the integration work is complete.

extern crate alloc;

use crate::common::{RegorusResult, RegorusStatus};

use alloc::string::String;
use core::sync::atomic::{AtomicBool, Ordering};
#[cfg(feature = "std")]
use std::{
    backtrace::Backtrace,
    cell::RefCell,
    panic::{self, AssertUnwindSafe},
};

#[cfg(feature = "std")]
thread_local! {
    // Stashes the formatted panic + backtrace for whichever call last panicked on this thread.
    static PANIC_BACKTRACE: RefCell<Option<String>> = const { RefCell::new(None) };
}

#[cfg(feature = "std")]
type PanicHook = dyn Fn(&panic::PanicHookInfo<'_>) + Sync + Send + 'static;

#[cfg(feature = "std")]
/// RAII helper that installs a per-call panic hook and restores the prior hook on drop.
struct PanicHookGuard {
    previous: Option<Box<PanicHook>>,
}

#[cfg(feature = "std")]
impl PanicHookGuard {
    fn install() -> Self {
        // Remember whatever hook the embedding application already registered.
        let previous = panic::take_hook();
        PANIC_BACKTRACE.with(|slot| {
            slot.replace(None);
        });
        // Install our temporary hook so we can capture a backtrace for this invocation.
        panic::set_hook(Box::new(|info| {
            let backtrace = Backtrace::force_capture();
            PANIC_BACKTRACE.with(|slot| {
                slot.replace(Some(format!(
                    "panic hook observed: {}\nbacktrace:\n{:#?}",
                    info, backtrace
                )));
            });
        }));
        Self {
            previous: Some(previous),
        }
    }
}

#[cfg(feature = "std")]
impl Drop for PanicHookGuard {
    fn drop(&mut self) {
        if let Some(previous) = self.previous.take() {
            // Restore the original panic hook before we return control to the host.
            panic::set_hook(previous);
        }
    }
}

static POISONED: AtomicBool = AtomicBool::new(false);

#[cfg(all(test, feature = "std"))]
static POISON_TEST_GATE: std::sync::RwLock<()> = std::sync::RwLock::new(());

#[cfg(all(test, feature = "std"))]
std::thread_local! {
    static POISON_TEST_GATE_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(all(test, feature = "std"))]
pub(crate) struct PoisonTestLock {
    lock: Option<std::sync::RwLockWriteGuard<'static, ()>>,
}

#[cfg(all(test, feature = "std"))]
impl Drop for PoisonTestLock {
    fn drop(&mut self) {
        self.lock.take();
        decrement_poison_test_gate_depth();
    }
}

#[cfg(all(test, feature = "std"))]
pub(crate) fn lock_poison_test_state() -> PoisonTestLock {
    debug_assert!(
        !poison_test_gate_is_held(),
        "the poison test gate cannot be upgraded from a nested guarded call"
    );
    let lock = POISON_TEST_GATE
        .write()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    increment_poison_test_gate_depth();
    PoisonTestLock { lock: Some(lock) }
}

#[cfg(all(test, feature = "std"))]
struct PoisonTestCallLock {
    lock: Option<std::sync::RwLockReadGuard<'static, ()>>,
}

#[cfg(all(test, feature = "std"))]
impl Drop for PoisonTestCallLock {
    fn drop(&mut self) {
        self.lock.take();
        decrement_poison_test_gate_depth();
    }
}

#[cfg(all(test, feature = "std"))]
fn poison_test_call_lock() -> PoisonTestCallLock {
    let nested = poison_test_gate_is_held();
    increment_poison_test_gate_depth();
    if nested {
        PoisonTestCallLock { lock: None }
    } else {
        let lock = POISON_TEST_GATE
            .read()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        PoisonTestCallLock { lock: Some(lock) }
    }
}

#[cfg(all(test, feature = "std"))]
fn poison_test_gate_is_held() -> bool {
    POISON_TEST_GATE_DEPTH.with(|depth| depth.get() > 0)
}

#[cfg(all(test, feature = "std"))]
fn increment_poison_test_gate_depth() {
    POISON_TEST_GATE_DEPTH.with(|depth| depth.set(depth.get().saturating_add(1)));
}

#[cfg(all(test, feature = "std"))]
fn decrement_poison_test_gate_depth() {
    POISON_TEST_GATE_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
}

/// Result of attempting to run `f` while guarding against unwinding.
pub(crate) enum GuardResult<T> {
    /// Closure completed successfully.
    Success(T),
    /// Closure panicked; contains a best-effort string payload.
    Panic(String),
}

pub(crate) fn with_unwind_guard<F>(f: F) -> RegorusResult
where
    F: FnOnce() -> RegorusResult,
{
    #[cfg(all(test, feature = "std"))]
    let _poison_test_call_lock = poison_test_call_lock();

    if is_poisoned() {
        return poisoned_result();
    }

    // The closure passed across this boundary closes over raw pointers and lock guards.
    // These types are not unwind safe by default and may become poisoned if a panic occurs.
    // We therefore use AssertUnwindSafe to get the compiler to accept the closure.
    // Upon unwind, we mark regorus as poisoned and disallow further use.
    #[cfg(feature = "std")]
    return finalize(catch_panic(f));

    #[cfg(not(feature = "std"))]
    return finalize(GuardResult::Success(f()));
}

#[cfg(feature = "std")]
fn catch_panic<F>(f: F) -> GuardResult<RegorusResult>
where
    F: FnOnce() -> RegorusResult,
{
    let _hook_guard = PanicHookGuard::install();
    match panic::catch_unwind(AssertUnwindSafe(f)) {
        Ok(value) => GuardResult::Success(value),
        Err(payload) => GuardResult::Panic(panic_message_to_string(payload)),
    }
}

#[cfg(all(test, feature = "std"))]
fn forget_hook_installation() {}

fn finalize(outcome: GuardResult<RegorusResult>) -> RegorusResult {
    match outcome {
        GuardResult::Success(result) => result,
        GuardResult::Panic(message) => {
            trip_poison();
            RegorusResult::err_with_message(RegorusStatus::Panic, message)
        }
    }
}

#[cfg(feature = "std")]
fn panic_message_to_string(payload: Box<dyn core::any::Any + Send + 'static>) -> String {
    let mut message = if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).into()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        String::from("regorus encountered panic")
    };

    if let Some(backtrace) = take_panic_backtrace() {
        message.push('\n');
        message.push_str(&backtrace);
    }

    message
}

#[cfg(feature = "std")]
fn take_panic_backtrace() -> Option<String> {
    PANIC_BACKTRACE.with(|slot| slot.borrow_mut().take())
}

fn poisoned_result() -> RegorusResult {
    RegorusResult::err_with_message(
        RegorusStatus::Poisoned,
        String::from("regorus is poisoned after a previous panic"),
    )
}

fn trip_poison() {
    POISONED.store(true, Ordering::Release);
}

pub(crate) fn is_poisoned() -> bool {
    POISONED.load(Ordering::Acquire)
}

pub(crate) fn reset_poison() {
    POISONED.store(false, Ordering::Release);
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::{catch_panic, forget_hook_installation, with_unwind_guard, GuardResult};
    use crate::common::{regorus_result_drop, RegorusResult, RegorusStatus};
    use std::panic;
    use std::sync::{mpsc, Mutex};
    use std::time::Duration;

    const TEST_PANIC_PREFIX: &str = "panic_guard_test:";
    static HOST_HOOK_PANICS: Mutex<Vec<String>> = Mutex::new(Vec::new());

    fn host_hook(info: &panic::PanicHookInfo<'_>) {
        let payload = info
            .payload()
            .downcast_ref::<&str>()
            .map(|s| s.to_string())
            .or_else(|| info.payload().downcast_ref::<String>().cloned())
            .unwrap_or_default();
        if payload.starts_with(TEST_PANIC_PREFIX) {
            HOST_HOOK_PANICS
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .push(payload);
        }
    }

    #[test]
    fn concurrent_guarded_panics_keep_their_messages_and_the_host_hook() {
        const THREADS: usize = 8;
        const ITERATIONS: usize = 40;

        // Serializes against every other guarded call in the test binary.
        let _poison_test_lock = super::lock_poison_test_state();
        HOST_HOOK_PANICS
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clear();
        let previous_hook = panic::take_hook();
        panic::set_hook(Box::new(host_hook));
        forget_hook_installation();

        let workers: Vec<_> = (0..THREADS)
            .map(|thread| {
                std::thread::spawn(move || {
                    let mut problems = Vec::new();
                    for iteration in 0..ITERATIONS {
                        let payload = format!("{TEST_PANIC_PREFIX} t{thread} i{iteration}");
                        let panics = (thread + iteration) % 2 == 0;
                        let expected = payload.clone();
                        let outcome = catch_panic(move || {
                            if panics {
                                panic!("{expected}");
                            }
                            RegorusResult::ok_void()
                        });
                        match (panics, outcome) {
                            (true, GuardResult::Panic(message)) => {
                                let observed = message.split_once("panic hook observed: ");
                                let own_location = observed.is_some_and(|(head, hook)| {
                                    head.starts_with(&payload)
                                        && hook.contains(&payload)
                                        && hook.contains(file!())
                                });
                                if !own_location {
                                    problems.push(format!("{payload}: message {message:?}"));
                                }
                            }
                            (false, GuardResult::Success(result)) => regorus_result_drop(result),
                            (true, GuardResult::Success(result)) => {
                                regorus_result_drop(result);
                                problems.push(format!("{payload}: panic not caught"));
                            }
                            (false, GuardResult::Panic(message)) => {
                                problems.push(format!("{payload}: unexpected panic {message:?}"));
                            }
                        }
                    }
                    problems
                })
            })
            .collect();
        let mut problems: Vec<String> = workers
            .into_iter()
            .flat_map(|worker| {
                worker
                    .join()
                    .unwrap_or_else(|_| vec!["worker panicked".into()])
            })
            .collect();

        let unguarded = format!("{TEST_PANIC_PREFIX} unguarded");
        let expected = unguarded.clone();
        let _ = std::thread::spawn(move || panic!("{expected}")).join();
        let host_panics = core::mem::take(
            &mut *HOST_HOOK_PANICS
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner()),
        );
        if host_panics != [unguarded] {
            problems.push(format!(
                "host hook must see only the unguarded panic, saw {} panics: {:?}",
                host_panics.len(),
                host_panics.iter().take(5).collect::<Vec<_>>()
            ));
        }

        // Restore before asserting: the hook cannot be changed while unwinding.
        panic::set_hook(previous_hook);
        forget_hook_installation();
        assert!(
            problems.is_empty(),
            "{} problems: {:#?}",
            problems.len(),
            &problems[..problems.len().min(10)]
        );
    }

    #[test]
    fn ordinary_guarded_calls_are_not_serialized_by_the_poison_test_gate() {
        let (first_entered_sender, first_entered_receiver) = mpsc::channel();
        let (second_entered_sender, second_entered_receiver) = mpsc::channel();

        let first = std::thread::spawn(move || {
            let result = with_unwind_guard(|| {
                let _ = first_entered_sender.send(());
                let second_entered = second_entered_receiver
                    .recv_timeout(Duration::from_secs(1))
                    .is_ok();
                RegorusResult::ok_bool(second_entered)
            });
            let success = matches!(result.status, RegorusStatus::Ok) && result.bool_value;
            regorus_result_drop(result);
            success
        });

        assert!(
            first_entered_receiver
                .recv_timeout(Duration::from_secs(1))
                .is_ok(),
            "first guarded call did not start"
        );

        let second = std::thread::spawn(move || {
            let result = with_unwind_guard(|| {
                let _ = second_entered_sender.send(());
                RegorusResult::ok_void()
            });
            let success = matches!(result.status, RegorusStatus::Ok);
            regorus_result_drop(result);
            success
        });

        let first_success = first.join().unwrap_or(false);
        let second_success = second.join().unwrap_or(false);
        assert!(second_success, "second guarded call did not complete");
        assert!(
            first_success,
            "ordinary guarded calls were serialized by the poison test gate"
        );
    }
}

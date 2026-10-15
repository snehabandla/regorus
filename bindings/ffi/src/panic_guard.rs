// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Helpers for catching panics inside the FFI layer.

extern crate alloc;

use crate::common::{RegorusResult, RegorusStatus};

use alloc::string::String;
use core::sync::atomic::{AtomicBool, Ordering};
#[cfg(feature = "std")]
use std::{
    backtrace::Backtrace,
    panic::{self, AssertUnwindSafe},
};

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
        .unwrap_or_else(std::sync::PoisonError::into_inner);
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
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        PoisonTestCallLock { lock: Some(lock) }
    }
}

#[cfg(all(test, feature = "std"))]
fn bypass_poison_test_gate() -> PoisonTestCallLock {
    increment_poison_test_gate_depth();
    PoisonTestCallLock { lock: None }
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
    #[cfg(feature = "std")]
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
    {
        let outcome = match panic::catch_unwind(AssertUnwindSafe(f)) {
            Ok(value) => GuardResult::Success(value),
            Err(payload) => GuardResult::Panic(panic_message_to_string(payload)),
        };
        finalize(outcome)
    }

    #[cfg(not(feature = "std"))]
    return finalize(GuardResult::Success(f()));
}

fn finalize(outcome: GuardResult<RegorusResult>) -> RegorusResult {
    match outcome {
        GuardResult::Success(result) => result,
        #[cfg(feature = "std")]
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

    message.push_str("\nbacktrace captured after unwind:\n");
    message.push_str(&format!("{:#?}", Backtrace::force_capture()));

    message
}

fn poisoned_result() -> RegorusResult {
    RegorusResult::err_with_message(
        RegorusStatus::Poisoned,
        String::from("regorus is poisoned after a previous panic"),
    )
}

#[cfg(feature = "std")]
fn trip_poison() {
    POISONED.store(true, Ordering::Release);
}

pub(crate) fn is_poisoned() -> bool {
    POISONED.load(Ordering::Acquire)
}

#[cfg(any(test, feature = "test-hooks"))]
pub(crate) fn reset_poison() {
    POISONED.store(false, Ordering::Release);
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::{
        bypass_poison_test_gate, lock_poison_test_state, reset_poison, with_unwind_guard,
        POISON_TEST_GATE,
    };
    use crate::common::{RegorusResult, RegorusStatus};
    use std::panic::{self, AssertUnwindSafe};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{mpsc, Arc};
    use std::thread;
    use std::time::Duration;

    #[test]
    fn concurrent_guards_preserve_the_host_panic_hook() {
        {
            let _poison_test_lock = lock_poison_test_state();
            reset_poison();
        }
        let ordinary_calls_lock = POISON_TEST_GATE
            .read()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let original_hook: Arc<dyn Fn(&panic::PanicHookInfo<'_>) + Sync + Send + 'static> =
            panic::take_hook().into();
        let host_hook_calls = Arc::new(AtomicUsize::new(0));
        let calls = Arc::clone(&host_hook_calls);
        let forwarded_hook = Arc::clone(&original_hook);
        let test_thread_id = thread::current().id();
        panic::set_hook(Box::new(move |info| {
            if thread::current().id() == test_thread_id {
                calls.fetch_add(1, Ordering::SeqCst);
            } else {
                forwarded_hook(info);
            }
        }));

        let outcome = panic::catch_unwind(AssertUnwindSafe(|| {
            let (a_entered_tx, a_entered_rx) = mpsc::channel();
            let (release_a_tx, release_a_rx) = mpsc::channel();
            let thread_a = thread::spawn(move || {
                let _bypass = bypass_poison_test_gate();
                let result = with_unwind_guard(|| {
                    a_entered_tx.send(()).expect("signal thread A entry");
                    RegorusResult::ok_bool(
                        release_a_rx.recv_timeout(Duration::from_secs(2)).is_ok(),
                    )
                });
                matches!(result.status, RegorusStatus::Ok) && result.bool_value
            });
            let a_entered = a_entered_rx.recv_timeout(Duration::from_secs(2)).is_ok();

            let (b_entered_tx, b_entered_rx) = mpsc::channel();
            let (release_b_tx, release_b_rx) = mpsc::channel();
            let thread_b = thread::spawn(move || {
                let _bypass = bypass_poison_test_gate();
                let result = with_unwind_guard(|| {
                    b_entered_tx.send(()).expect("signal thread B entry");
                    RegorusResult::ok_bool(
                        release_b_rx.recv_timeout(Duration::from_secs(2)).is_ok(),
                    )
                });
                matches!(result.status, RegorusStatus::Ok) && result.bool_value
            });
            let b_entered = b_entered_rx.recv_timeout(Duration::from_secs(2)).is_ok();

            let _ = release_a_tx.send(());
            let _ = release_b_tx.send(());
            let a_succeeded = thread_a.join().unwrap_or(false);
            let b_succeeded = thread_b.join().unwrap_or(false);

            drop(ordinary_calls_lock);
            let _poison_test_lock = lock_poison_test_state();
            reset_poison();
            let probe = panic::catch_unwind(AssertUnwindSafe(|| {
                panic!("probe the host hook after overlapping guards");
            }));
            let guarded_panic = with_unwind_guard(|| {
                panic!("probe panic containment without replacing the host hook")
            });
            let guarded_panic_caught = matches!(guarded_panic.status, RegorusStatus::Panic);
            crate::common::regorus_result_drop(guarded_panic);
            let observed_calls = host_hook_calls.load(Ordering::SeqCst);
            reset_poison();

            (
                a_entered,
                b_entered,
                a_succeeded,
                b_succeeded,
                probe.is_err(),
                guarded_panic_caught,
                observed_calls,
            )
        }));

        let _installed_hook = panic::take_hook();
        panic::set_hook(Box::new(move |info| original_hook(info)));
        {
            let _poison_test_lock = lock_poison_test_state();
            reset_poison();
        }

        let (
            a_entered,
            b_entered,
            a_succeeded,
            b_succeeded,
            probe_panicked,
            guarded_panic_caught,
            observed_calls,
        ) = outcome.unwrap_or_else(|payload| panic::resume_unwind(payload));
        assert!(a_entered, "thread A did not enter its guard");
        assert!(
            b_entered,
            "thread B did not overlap thread A inside its guard"
        );
        assert!(a_succeeded, "thread A did not complete");
        assert!(b_succeeded, "thread B did not complete");
        assert!(probe_panicked, "the probe panic must be caught");
        assert!(guarded_panic_caught);
        assert_eq!(
            observed_calls, 2,
            "overlapping calls and a guarded panic must preserve the host panic hook"
        );
    }
}

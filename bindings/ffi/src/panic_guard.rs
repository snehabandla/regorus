// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Helpers for catching panics inside the FFI layer.
//!
//! A panic inside a guarded call is caught, marks regorus as poisoned, and is
//! returned as a `Panic` result. The process-global panic hook is never swapped
//! per call, because concurrent calls would race on it. Instead, the first
//! guarded call installs one hook that chains to the hook installed before it:
//! while the current thread is inside a guard it records the panic location
//! (and, when `RUST_BACKTRACE` enables it, a backtrace) for the returned
//! message, then calls the previous hook. A hook installed later by the host
//! replaces it; panics are still caught, only without a location. Installing
//! takes the current hook and sets the chaining one in two steps, so a hook
//! the host sets on another thread between them is overwritten; set host hooks
//! before the first FFI call.

extern crate alloc;

use crate::common::{RegorusResult, RegorusStatus};

use alloc::string::String;
use core::sync::atomic::{AtomicBool, Ordering};
#[cfg(feature = "std")]
use std::panic::{self, AssertUnwindSafe};

static POISONED: AtomicBool = AtomicBool::new(false);

// Tests share the process-global poison flag. Every guarded call holds this
// gate for reading; a test that trips or resets poison takes it for writing,
// so ordinary FFI tests never observe another test's poison window.
#[cfg(all(test, feature = "std"))]
static POISON_TEST_GATE: std::sync::RwLock<()> = std::sync::RwLock::new(());

#[cfg(all(test, feature = "std"))]
std::thread_local! {
    static POISON_TEST_GATE_DEPTH: core::cell::Cell<usize> = const { core::cell::Cell::new(0) };
}

#[cfg(all(test, feature = "std"))]
pub(crate) struct PoisonTestLock {
    lock: Option<std::sync::RwLockWriteGuard<'static, ()>>,
}

#[cfg(all(test, feature = "std"))]
impl Drop for PoisonTestLock {
    fn drop(&mut self) {
        // A test that fails while holding the lock must not leave regorus
        // poisoned for the tests that run after it.
        reset_poison();
        self.lock.take();
        decrement_poison_test_gate_depth();
    }
}

/// Take exclusive access to process-global FFI state (poison flag, panic
/// hook, global limits) for the rest of the test.
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

/// Let a thread spawned by a test that already holds the gate make guarded
/// calls without waiting for that gate.
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

/// Records where a guarded panic happened, through one chaining panic hook.
#[cfg(feature = "std")]
mod location_hook {
    use alloc::format;
    use alloc::string::String;
    use core::cell::{Cell, RefCell};
    use core::sync::atomic::{AtomicBool, Ordering};
    use std::backtrace::{Backtrace, BacktraceStatus};
    use std::panic::{self, PanicHookInfo};
    use std::sync::{Mutex, PoisonError};

    static INSTALLED: AtomicBool = AtomicBool::new(false);
    static INSTALL_LOCK: Mutex<()> = Mutex::new(());

    std::thread_local! {
        static GUARD_DEPTH: Cell<usize> = const { Cell::new(0) };
        static LAST_PANIC: RefCell<Option<String>> = const { RefCell::new(None) };
    }

    /// Install the chaining hook once per process (until a test forgets it).
    pub(super) fn ensure_installed() {
        if INSTALLED.load(Ordering::Acquire) || std::thread::panicking() {
            return;
        }
        let _install = INSTALL_LOCK.lock().unwrap_or_else(PoisonError::into_inner);
        if INSTALLED.load(Ordering::Acquire) {
            return;
        }
        let previous = panic::take_hook();
        panic::set_hook(alloc::boxed::Box::new(move |info| {
            record(info);
            previous(info);
        }));
        INSTALLED.store(true, Ordering::Release);
    }

    /// Tests that replace the process hook call this so the next guarded call
    /// installs the chaining hook again.
    #[cfg(test)]
    pub(crate) fn forget_installation() {
        INSTALLED.store(false, Ordering::Release);
    }

    fn record(info: &PanicHookInfo<'_>) {
        let guarded = GUARD_DEPTH
            .try_with(|depth| depth.get() > 0)
            .unwrap_or(false);
        if !guarded {
            return;
        }
        let mut details = info.location().map_or_else(
            || String::from("panicked at an unknown location"),
            |location| {
                format!(
                    "panicked at {}:{}:{}",
                    location.file(),
                    location.line(),
                    location.column()
                )
            },
        );
        let backtrace = Backtrace::capture();
        if backtrace.status() == BacktraceStatus::Captured {
            details.push_str(&format!("\nbacktrace:\n{backtrace}"));
        }
        let _ = LAST_PANIC.try_with(|slot| {
            if let Ok(mut slot) = slot.try_borrow_mut() {
                *slot = Some(details);
            }
        });
    }

    /// Marks the current thread as inside a guard for the scope's lifetime.
    pub(super) struct GuardScope;

    impl GuardScope {
        pub(super) fn enter() -> Self {
            // `try_with`: a call made while thread-locals are being destroyed
            // must not panic before `catch_unwind` is in place.
            let outermost = GUARD_DEPTH
                .try_with(|depth| {
                    let current = depth.get();
                    depth.set(current.saturating_add(1));
                    current == 0
                })
                .unwrap_or(false);
            if outermost {
                // Drop details of a panic that something inside an earlier
                // guard caught itself, so they are not attributed to this call.
                let _ = LAST_PANIC.try_with(|slot| {
                    if let Ok(mut slot) = slot.try_borrow_mut() {
                        slot.take();
                    }
                });
            }
            Self
        }
    }

    impl Drop for GuardScope {
        fn drop(&mut self) {
            let _ = GUARD_DEPTH.try_with(|depth| depth.set(depth.get().saturating_sub(1)));
        }
    }

    /// The details recorded for the most recent guarded panic on this thread.
    pub(super) fn take_last_panic() -> Option<String> {
        LAST_PANIC
            .try_with(|slot| slot.try_borrow_mut().ok().and_then(|mut slot| slot.take()))
            .ok()
            .flatten()
    }
}

#[cfg(all(test, feature = "std"))]
pub(crate) use location_hook::forget_installation as forget_panic_hook_installation;

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
        location_hook::ensure_installed();
        let caught = {
            let _scope = location_hook::GuardScope::enter();
            panic::catch_unwind(AssertUnwindSafe(f))
        };
        let outcome = match caught {
            Ok(value) => GuardResult::Success(value),
            Err(payload) => {
                // The unwind has already released the engine's locks, so
                // publish poison before spending time on diagnostics.
                trip_poison();
                GuardResult::Panic(panic_message(payload.as_ref()))
            }
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
            RegorusResult::err_with_message(RegorusStatus::Panic, message)
        }
    }
}

#[cfg(feature = "std")]
fn panic_message(payload: &(dyn core::any::Any + Send + 'static)) -> String {
    let mut message = if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).into()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        String::from("regorus encountered panic")
    };

    if let Some(details) = location_hook::take_last_panic() {
        message.push('\n');
        message.push_str(&details);
    }

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
        bypass_poison_test_gate, forget_panic_hook_installation, location_hook,
        lock_poison_test_state, reset_poison, with_unwind_guard,
    };
    use crate::common::{RegorusResult, RegorusStatus};
    use core::ffi::CStr;
    use std::panic::{self, AssertUnwindSafe};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{mpsc, Arc};
    use std::thread;
    use std::time::Duration;

    #[test]
    fn concurrent_guards_preserve_the_host_panic_hook() {
        // Hold the gate for the whole test, including the hook restore, so no
        // other test sees or replaces the counting hook. The spawned threads
        // bypass the gate.
        let _poison_test_lock = lock_poison_test_state();
        reset_poison();
        // Snapshot the hook only after the chaining hook is in place, so
        // restoring the snapshot keeps it.
        location_hook::ensure_installed();
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
        reset_poison();

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

    #[test]
    fn guarded_panic_reports_its_location_and_poisons() {
        let _poison_test_lock = lock_poison_test_state();
        reset_poison();
        // A host hook installed before regorus must keep running: the hook
        // regorus installs on the next guarded call chains to it.
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
        forget_panic_hook_installation();

        let line = line!() + 1;
        let result = with_unwind_guard(|| panic!("located ffi panic"));
        let host_calls_after_guarded_panic = host_hook_calls.load(Ordering::SeqCst);
        assert!(matches!(result.status, RegorusStatus::Panic));
        assert!(super::is_poisoned(), "a guarded panic must poison regorus");
        // SAFETY: a panic result owns a valid NUL-terminated message.
        let message = unsafe { CStr::from_ptr(result.error_message) }
            .to_str()
            .expect("message is UTF-8")
            .to_string();
        crate::common::regorus_result_drop(result);
        reset_poison();

        assert!(message.starts_with("located ffi panic\n"), "{message}");
        assert!(
            message.contains(&format!("panicked at {}:{line}:", file!())),
            "{message}"
        );
        assert!(!message.contains("captured after unwind"), "{message}");

        // A panic caught inside a guarded closure records its location; it
        // must not be attributed to a later guarded panic that the hook does
        // not record (here, because the host replaced the hook).
        let inner_line = line!() + 2;
        let inner_caught = with_unwind_guard(|| {
            let _ = panic::catch_unwind(|| panic!("caught inside the guard"));
            RegorusResult::ok_void()
        });
        assert!(matches!(inner_caught.status, RegorusStatus::Ok));
        crate::common::regorus_result_drop(inner_caught);
        let chaining_hook: Arc<dyn Fn(&panic::PanicHookInfo<'_>) + Sync + Send + 'static> =
            panic::take_hook().into();
        let other_threads = Arc::clone(&chaining_hook);
        panic::set_hook(Box::new(move |info| {
            // Silence only this thread; other tests keep their panic output.
            if thread::current().id() != test_thread_id {
                other_threads(info);
            }
        }));
        let next = with_unwind_guard(|| panic!("unrecorded ffi panic"));
        let _silencing_hook = panic::take_hook();
        panic::set_hook(Box::new(move |info| chaining_hook(info)));
        // SAFETY: as above.
        let next_message = unsafe { CStr::from_ptr(next.error_message) }
            .to_str()
            .expect("message is UTF-8")
            .to_string();
        crate::common::regorus_result_drop(next);
        reset_poison();
        assert_eq!(next_message, "unrecorded ffi panic");
        assert!(!next_message.contains(&format!(":{inner_line}:")));

        // Restore the hook from before this test; the next guarded call
        // installs the chaining hook over it again.
        let _chaining_and_host_hooks = panic::take_hook();
        panic::set_hook(Box::new(move |info| original_hook(info)));
        forget_panic_hook_installation();
        assert_eq!(
            host_calls_after_guarded_panic, 1,
            "the host hook must run once for a guarded panic"
        );
    }
}

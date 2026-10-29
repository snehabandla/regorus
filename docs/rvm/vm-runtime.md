# VM Runtime Walkthrough

This document explains the runtime architecture implemented under
`src/rvm/vm`. It focuses on the `RegoVM` struct, execution modes, and the
responsibilities of each support module.

---

## 1. RegoVM structure

`src/rvm/vm/machine.rs` defines the public entry point. The table below maps its
fields to responsibilities.

| Field                                 | Purpose                                                     | Related modules |
| :------------------------------------ | :---------------------------------------------------------- | :-------------- |
| `registers: Vec<Value>`               | Active register window for the current frame.               | `execution.rs`, `dispatch.rs` |
| `pc: usize`                           | Instruction pointer in run-to-completion mode.              | `execution.rs` |
| `program: Arc<Program>`               | Loaded program artifact.                                    | `program/core.rs` |
| `compiled_policy`                     | Optional legacy default-rule support.                       | `crate::CompiledPolicy` |
| `rule_cache: Vec<(bool, Value)>`      | Memoized rule results (bool = computed).                    | `rules.rs` |
| `data`, `input`                       | Global documents injected by host.                          | `dispatch.rs`, `virtual_data.rs` |
| `loop_stack`                          | Stack of `LoopContext` for run-to-completion loops.         | `loops.rs` |
| `call_rule_stack`                     | Stack of `CallRuleContext` for nested rule calls.           | `rules.rs` |
| `register_stack`                      | Saves prior register windows during run-to-completion rule calls. | `rules.rs`, `state.rs` |
| `comprehension_stack`                 | Active `ComprehensionContext` objects.                      | `comprehension.rs` |
| `base_register_count`                 | Root window size derived from program metadata.             | `load_program` |
| `register_window_pool`                | Recycled register vectors to reduce allocations.            | `state.rs`, `rules.rs` |
| `max_instructions`, `executed_instructions` | Instruction budget and counter.                           | `execution.rs` |
| `evaluated`                           | Cache for virtual document lookups.                         | `virtual_data.rs` |
| `cache_hits`                          | Counters aiding diagnostics.                                | `virtual_data.rs` |
| `execution_stack`                     | Explicit frame stack for suspendable mode.                  | `execution_model.rs` |
| `execution_state`                     | `ExecutionState` enum capturing Ready/Running/Suspended/Error/Completed. | `execution_model.rs`, `execution.rs` |
| `breakpoints`                         | Set of PCs that trigger suspension.                         | `execution_model.rs` |
| `step_mode`                           | Enables single-step suspension after each instruction.      | `execution.rs` |
| `host_await_responses`                | Pre-scripted responses keyed by identifier (run-to-completion). | `dispatch.rs` |
| `execution_mode`                      | `RunToCompletion` or `Suspendable`.                         | `execution.rs` |
| `frame_pc_overridden`                 | Tracks manual PC updates inside frames.                     | `execution.rs`, `loops.rs`, `comprehension.rs` |
| `strict_builtin_errors`               | Configures builtin failure handling (error vs `undefined`).  | `machine.rs`, `arithmetic.rs`, `dispatch.rs` |

### Key methods

- `new` / `new_with_policy`: initialise VM with default register windows and
  instruction limits.
- `load_program`: attaches a compiled `Program`, resizes registers, seeds rule
  cache and resets counters.
- `set_data` / `set_input`: inject host documents. `set_data` runs
  `Program::check_rule_data_conflicts` to guard against rule/data collisions.
- `set_max_instructions`, `set_execution_mode`, `set_step_mode`: configure
  runtime policy.
- `set_host_await_responses`: used in run-to-completion mode when host await
  responses are known ahead of time.
- `set_strict_builtin_errors`: toggles builtin failure semantics between
  `VmError::ArithmeticError` and returning `Value::Undefined`.
- Accessors (`get_pc`, `get_registers`, `get_loop_stack`, etc.) aid debugging
  and visualisation tooling.

---

## 2. Execution modes

### Run-to-completion

- Entry path: `execute()` or `execute_entry_point_by_*` when
  `ExecutionMode::RunToCompletion`.
- `execute_run_to_completion` resets state, marks `ExecutionState::Running` and
  calls `jump_to(start_pc)`.
- `jump_to` loops over instructions, updating `pc` and calling
  `execute_instruction`. The loop stops on `Return`, `Break`, or `VmError`.
  `Break` (emitted by `RuleReturn` and `DestructuringSuccess`) returns
  register 0 to the caller for compatibility with rule evaluation.
- Suspension is not allowed; encountering an instruction that would suspend
  (e.g. `HostAwait`) raises an internal error.
- Instruction budgets trigger `VmError::InstructionLimitExceeded` and switch the
  state to `ExecutionState::Error`.

### Suspendable

- Entry path: same public API, but the VM calls `run_stackless_from`.
- `run_stackless_from` pushes an initial `ExecutionFrame::main(start_pc, 0)`
  onto `execution_stack` and dispatches instructions via `run_stackless_loop`.
- Each frame tracks its own `pc` and `FrameKind` (`Main`, `Rule`, `Loop`,
  `Comprehension`).
- `RuleFrameData` carries scheduling cursors, register window sizing, and saved
  copies of the caller's registers, stacks and (with `explanations`) register
  provenance so finalisation can restore the original context; the result
  reaches the caller with the provenance of the definition that produced it,
  as in run-to-completion.
- With explanations enabled, a rule whose result is cached is evaluated again
  on each call, as in run-to-completion, so the call records its conditions and
  provenance. A `HostAwait` inside such a rule therefore suspends on every call.
- Suspension: `InstructionOutcome::Suspend` records a `SuspendReason` (host
  await, breakpoint, step) and stores the last result snapshot. Host code calls
  `resume(resume_value)` to continue.
- Completion: when `execution_stack` becomes empty the VM sets
  `ExecutionState::Completed { result }`.

`execution_model.rs` defines the frame types and state machine:

- `ExecutionFrame`: captures the frame-local `pc` together with its
  `FrameKind` payload.
- `RuleFrameData`: tracks rule index, scheduling phase, register window sizing,
  and the saved caller state (`saved_registers`, `saved_loop_stack`,
  `saved_comprehension_stack`).
- `SuspendReason`: currently surfaced values are host await, breakpoint, and
  step; additional variants (`SuspendInstruction`, `InstructionLimit`,
  `External`) are reserved for future instructions.

---

## 3. Instruction dispatch

`dispatch.rs` routes each `Instruction` variant through layered helpers
(`execute_load_and_move`, `execute_arithmetic_instruction`, `execute_call_instruction`, etc.). Control
flow hinges on the `InstructionOutcome` enum:

- `Continue`: normal execution; the caller increments the frame `pc`.
- `Return(Value)`: unwinds the current rule/function frame, propagating the
  value upward.
- `Break`: used for rule-specific constructs (destructuring success, rule
  return) to exit to the owning frame without returning a value.
- `Suspend { reason }`: used exclusively in suspendable mode.

Arithmetic and comparison opcodes live in `arithmetic.rs`, honouring
`strict_builtin_errors` when operand types differ. Collection, loop, and
virtual-data operations share helpers that convert `Value` variants with runtime
type checking. Errors become `VmError` variants to ensure consistent reporting.
`Halt` returns the value stored in register 0, allowing bytecode to terminate
early without suspending.

---

## 4. Loops and comprehensions

`loops.rs` implements iteration. Major components:

- `LoopContext`: stores iteration state (`IterationState` enum), key/value/result
  registers, body and exit PCs, counters, and loop mode.
- `IterationState`: variants for arrays, objects, sets. Tracks progress for both
  execution modes.
- `LoopMode`: `Any`, `Every`, `ForEach` controls short-circuit behaviour.

`execute_loop_start` initialises iteration, pushing the context onto
`loop_stack` (run-to-completion) or embedding it into a `FrameKind::Loop`
(suspendable). `LoopParams` carries the bytecode offsets, registers, and
destinations required by the instruction. `LoopNext` evaluates the previous
iteration outcome, updates `success_count`, advances the iterator, overrides
the caller's PC when needed, and decides whether to continue or exit.

`comprehension.rs` parallels `loops.rs` but maintains builder collections in
`ComprehensionContext`. The context stores:

- Builder value (array, set, object).
- Pending key/value registers.
- `body_start` / `comprehension_end` PCs.
- `iteration_state` for nested loops bound to the comprehension.

`ComprehensionYield` writes to the builder, respecting set uniqueness and object
key/value pairing. `ComprehensionEnd` publishes the result to `result_reg` and
pops the context.

---

## 5. Rule execution and caching

`rules.rs` and `functions.rs` coordinate rule calls:

- `execute_call_rule` dispatches based on execution mode. Both paths consult
  `rule_cache` and short-circuit if the result is already available.
- Run-to-completion (`execute_call_rule_common`): swaps the active register,
  loop, and comprehension stacks; pushes them onto `register_stack`; and drives
  bodies via `jump_to`. Successful results are cached for non-function rules.
- Suspendable (`execute_call_rule_suspendable`): builds a `RuleFrameData`
  containing saved registers/stacks and pushes a `FrameKind::Rule` so the
  stackless loop can schedule destructuring, bodies, and finalisation.
- `execute_rule_init` writes the rule result register to `Value::Undefined`
  (or initialises sets/objects) before running the bodies and records the
  result register in the active `CallRuleContext`.
- `execute_rule_return` lets the scheduler finalise the frame and propagate the
  cached value to the caller.
- `functions.rs::execute_function_call` prepares argument registers and delegates
  to `execute_call_rule*`, enforcing arity via `BuiltinInfo` metadata.

Rule destructuring relies on `CallRuleContext`,
`RuleFramePhase::ExecutingDestructuring`, and the `DestructuringSuccess`
instruction to detect when pattern matching succeeded before entering the body.

---

## 6. Virtual data lookups

`virtual_data.rs` implements `VirtualDataDocumentLookup` and caches intermediate
path results in the VM's `evaluated` field (using `Value::Undefined` as a
sentinel) to avoid repeated rule evaluations. The compiler may set
`Program::needs_runtime_recursion_check`; the runtime currently relies on the
instruction budget and caching to prevent runaway recursion. Paths consist of
literals and register values supplied via `VirtualDataDocumentLookupParams`.

`ChainedIndex` follows a similar pattern but operates on register roots instead
of the global `data` namespace.

---

## 7. Error handling and diagnostics

`errors.rs` defines the `VmError` enum. Common variants include:

- `InstructionLimitExceeded`
- `LiteralIndexOutOfBounds`
- `RegisterNotArray` / `RegisterNotObject`
- `InvalidEntryPointIndex` / `EntryPointNotFound`
- `ArithmeticError`
- `RuleDataConflict`
- `HostAwaitResponseMissing`
- `Internal(String)` for invariant violations

`execution.rs::handle_instruction_error` centralises error propagation. In
suspendable mode it unwinds frames while preserving partial results where
possible. Run-to-completion mode returns the error immediately.

`state.rs` provides helpers to reset the VM and emit debug snapshots used in
assertion messages. When an internal invariant fails, the error message includes
`self.get_debug_state()` to help diagnose the issue.

---

## 8. Operational guidance

With the `explanations` feature enabled, causality reports for bare-reference
negations such as `not resource.properties.enabled` include the referenced
operand's concrete `left.provenance`. `left.absent: true` distinguishes an
undefined reference from a defined `false` value; the field is omitted for
defined values. `left.value` retains the boolean guard result, not the original
referenced value. Secret-path redaction still applies to `left.value`; it does
not hide `absent`, so a report can distinguish a missing sensitive field from a
defined `false` one. When `assume_unknown_input` is set and the path falls under
a configured unknown prefix, `absent` is omitted: the value is unknown, not known
to be missing. Negated rule or function calls (`not flag`, `not f(x)`) are
not bare references and do not receive these fields. Capture is limited to a
reference evaluated directly inside the negation (`not r.x`, `not input[k]`); a
negated local alias (`x := input.a; not x`) receives no reference attribution,
and an unresolved dynamic key receives no concrete path or absence marker. These
report fields do not change evaluation results or the VM's register provenance.

Comparison conditions (`==`, `!=`, `<`, `<=`, `>`, `>=`, `in`), whether positive
or negated, report the evaluated operands: `left`/`right` carry each operand's
value and, when it came from input or data, its concrete provenance; a literal
operand has no provenance. Ordinary comparisons keep source order; membership
(`x in c`) always reports `left` = the value and `right` = the collection. This
applies to failed and Undefined comparisons too (an Undefined operand's value is
`<undefined>`). Only condition guards are captured this way; a definedness guard
on a comparison result (`_ = (a != b)`) keeps the boolean it checked.

In `Redacted` value mode (the default), the report applies the same rules to
every value it takes from evaluation: condition operands of any kind, loop
witness samples, the values embedded in condition text (`[matched: …]`,
`[loop: … sample: …]`), the `assumed_value` of causality `assumptions`, and the
results of helper rules. Redaction is best-effort defense in depth, not a
secrecy guarantee: it decides from where a value was read (its runtime path)
and from names, and a value computed from a secret by a builtin (`lower`,
`sprintf`, `object.get`), a comprehension, `walk` or collection construction
carries no path, so only the nested-name check below applies to it. A
comparison or other result that copies an operand's path inherits that path's
sensitivity. Tracking sensitivity through computation is a separate feature
(RG-R3). A value whose runtime path has a sensitive-named
segment is replaced with `<redacted>`, and so is a value at or under the path of
a sensitive pair's `value` (below); the keys a runtime path shows beneath its
first sensitive segment are themselves hidden, as `["<redacted>"]` (numeric
indices are kept; compound keys are hidden), because the keys of a secret collection are secret too. Values under sensitive-named object keys nested
anywhere inside a value are replaced with `<redacted>`, and the value is marked
`redacted: true`; a secret inside a compound (non-string) object key cannot be
rewritten safely, so the whole enclosing object is redacted. In an object whose
`name` entry is a sensitive name (`{"name": "DB_PASSWORD", "value": …}`, as in
ARM `appSettings` or container `env`), the `value` entry is sensitive too: while
the object is shown whole, and also once the policy reads the `value` on its own
(`s.value`, or iterating the object), because the VM records the path it was read
from. The VM also records the string keys of objects (and the string elements of
sets) it iterates at a sensitive path, and a reported top-level string equal to
one of them is hidden, since a key has no path of its own; strings nested inside
a reported value are checked by name only. Both records are kept only in `Redacted` mode and hold up to 1,024 entries
each. Past the pair-path cap, every path with a `value` segment and every path
the report cannot parse is treated as sensitive; past the key cap, every string
operand without a runtime path is. The path text of a causality assumption
(`assumed_holds`) is masked like its `input_path`.
Two-operand conditions (comparisons, membership and string-predicate builtins)
are also redacted as a pair: if either operand's path is sensitive, both values
are redacted, because a matching or containing operand can reveal the other. They
are identified from the compiled condition, so pairing still applies if the
trace's value capacity drops one operand. A loop witness sample is redacted by
its loop's collection path (a sensitive path hides the key and the value) and by
its key (a sensitive-named key hides the value), and by the path the sampled
value was read from (a sensitive pair's `value` is hidden); a key or value equal
to a recorded key of a sensitive collection is hidden too. A loop over a
computed collection has no path, so only these by-name and by-value checks apply. An
assumed value is hidden when the assumed input path or the value's own path is
sensitive. A helper rule is one the caller did not query: neither an entry point
nor a rule under an entry-point package. Its `result` and emission `result`s are
hidden whole when they were read from a sensitive path (the VM records where a
rule's result and each emitted value came from, keeping each value with the
provenance of the definition that produced it). Because one reported `result`
stands for every call of a function, it is hidden when any successful call
returned a value from a sensitive path. Elements of a collection result that
equal a sensitive emitted value or a recorded key are hidden, at any depth for
partial-object results (a multi-value head, `h[k] contains v`, nests them), and
an object result keyed by a recorded key is hidden whole. When only the rule's name is
sensitive, its value is hidden whole unless it is a boolean or null, which
describe a setting rather than hold one. Otherwise nested secrets are sanitized.
A rewritten rule `result`, emission `result` or `assumed_value` is marked
`redacted: true`.

Redaction is best effort: it recognizes sensitive names, not secret-looking
values. Names are compared after lowercasing and dropping `-`, `_` and spaces,
and match when they contain one of `password`, `passwd`, `pwd`, `passphrase`,
`secret`, `token`, `apikey`, `jwt`, `credential`, `privatekey`, `accesskey`,
`connectionstring`, `securevalue` or `protectedsettings`, or when they end with
`accountkey`, `sharedkey`, `primarykey`, `secondarykey` or `subscriptionkey` (so
`storageAccountKey` matches but the setting `allowSharedKeyAccess` does not); a
path is checked one segment at a time. Policy outputs (`query_result` and the `result` values of
queried rules and their emissions) are what the policy author chose to return and
are not redacted, so a policy that returns a whole resource returns its secrets
too. Partial-evaluation residuals are not redacted either: a residual value is
part of the computed answer. Use `Full` only where the report is as trusted as
the input.

A condition carries a loop `witness` (iteration count, success count and the
first successful key and value; the key is the element's key or index even for
an `every` that declares no key variable, and the element carries a runtime path) only for a completed loop that is accountable to
what the condition list explains. A loop is anchored at the last condition its
own rule body recorded while the loop ran, never at a condition of a rule or
function it called or one recorded before it started; a loop that recorded no
condition of its own has no anchor and is never summarized. A definition (or a
rule-less program, or a helper body) carries the latest loop anchored among its
reported conditions. An emission or derivation additionally requires that the
loop finished before the value was emitted and, for a loop nested in another
loop, that its enclosing iteration was still running at the emission; so the loop
that produced a value is summarized on its definition, never on the emission, and
an inner loop finished in an earlier iteration of the outer loop is not
summarized on a later iteration's emission. A loop that completes inside one
derivation (for example an `every` over the current resource's ports) is
summarized there. An `every` that fails early counts the failing iteration. In
`Compact` detail a partial-set rule with emissions, and every rule in
`RuleSummary` scope, omits its definitions and so carries no loop summary.

Operands of two-operand conditions are capped at 100 elements, counted across
all nesting levels. A larger collection is reported as the prefix that fits, with
`truncated: true` and `length` set to its original top-level element count; both
fields are omitted for operands that fit. Truncation happens before redaction, so
only the emitted prefix is walked. Truncation never affects evaluation: a value
can match an element beyond the reported prefix.

Backward operand scans (static and runtime) stop at rule-definition boundaries,
because registers are numbered per definition.

Conditions evaluated inside a comprehension body, an `every` body, or the
expression of a `not` carry `scopes`, the enclosing constructs from outer to inner
(`"comprehension"`, `"every"`, `"negation"`); rule-level conditions omit the field.
In `storage := [r | some r in input.resources; r.type == "S"]` the `r` binding and
the `r.type` check are scoped `["comprehension"]`: they describe one sample
element, not the subject of the rule. The comprehension's own result binding
(`storage`), the guard that an `every` holds, and the negated guard of a `not` are
rule-level. Scopes are derived from the bytecode brackets (`ComprehensionBegin`
to its end, `LoopStart` in `every` mode to its end, `NegationBegin` to `Not`).
They are relative to the body that recorded the condition: a helper's
`helper_conditions` are scoped within the helper, and the calling condition's
`scopes` apply on top. Scopes describe where a condition executes: a loop that
the compiler hoists out of a `not` (as in `not [x | ...][_]`) runs before the
negation, so its conditions do not carry `negation`. Azure Policy conditions carry no `scopes`. Like the other
static explanation metadata, scopes are computed during compilation and are not
serialized with a `Program`: a deserialized program reports no `scopes` (and no
condition text), so recompile before requesting explanations. Only the first body
of each rule definition is analyzed statically; conditions in later `else` bodies
carry no static metadata, including scopes.

A partial-set value can be emitted by several derivations, for example a constant
message produced once per non-compliant resource. By default each emission
explains only its first derivation. Setting `ExplanationSettings::max_derivations`
above 1 (or calling `set_explanation_max_derivations` after
`set_explanation_settings`, which resets it; the C ABI export is
`regorus_rvm_set_explanation_max_derivations`) adds `derivations` to every
partial-set emission: up to that many distinct derivations, in trace order and
including the first, whose definition is the emission's top-level
`definition_index`:

```json
{"index": 0, "definition_index": 0, "result": "storage must set tls",
 "conditions": [...],
 "derivations": [{"definition_index": 0, "conditions": [...]}, ...],
 "derivation_count": 3, "derivations_truncated": true}
```

The first derivation's `conditions` equal the emission's top-level
`conditions`, and each derivation carries only the loop witnesses that finished
within it.

Two derivations are the same, and counted once, only when their definition and
every condition, as presented, are equal: values hidden by redaction, operand
truncation or `PrimaryOnly` filtering are not compared. For `Compact` reports
equality is judged before the operands are stripped, so derivations that print
alike can still be distinct. `derivation_count` (the number of distinct
derivations) and `derivations_truncated` appear only when the list was cut or
may be incomplete. Every derivation of a repeated value is materialized, one at
a time, to decide whether it is distinct; beyond the cap only a 128-bit
fingerprint (16 bytes) is kept for each distinct one, so report time grows with
the number of derivations and their condition windows even when the list is
cut. Comparison against kept derivations is linear in the cap, so choose a
small cap rather than "unlimited". If the trace runs out of value slots, an
emission whose value was lost may have been a derivation of this value: the
list is then marked `derivations_truncated` and `derivation_count` is
approximate, as it is when a derivation past the cap cannot be fingerprinted.
`SingleEmission` targeting is unchanged and collects every derivation of the
target value. With `AllContributing`, an emission's window runs from the start
of the rule body, so a later derivation also lists the conditions of earlier
loop iterations; the iteration that emitted is the last one in its window, and
report time grows quadratically in the window size. As with every report field,
the trace is cleared only when a report is taken, so executing twice before
taking it explains both executions. `0` is treated as `1`, and the default
output is unchanged. The setting is honored by the Rust `RegoVM` and `Engine`
(through `ExplanationSettings`) and exposed by the RVM C ABI and C# bindings; the
interpreter-engine C ABI/C# bindings and wasm keep the default.

- **Instruction budgets**: adjust via `set_max_instructions` when running
  untrusted policies. Inspect `executed_instructions` after completion.
- **Breakpoints & stepping**: populate `breakpoints` with bytecode PCs (see the
  assembly listing) and enable `set_step_mode(true)` to pause after each
  instruction.
- **Host await**: in run-to-completion mode, configure `set_host_await_responses`
  before execution. In suspendable mode, expect `ExecutionState::Suspended {
  reason: HostAwait { .. } }` and resume with the chosen value.
- **Builtin strictness**: `set_strict_builtin_errors(true)` reports type
  mismatches as `VmError::ArithmeticError`; leave it `false` to coerce results
  to `Value::Undefined`.
- **State inspection**: use getters (`get_registers`, `get_call_stack`,
  `get_loop_stack`, `get_cache_hits`) to instrument evaluation or build
  debugging UIs. `get_debug_state()` provides a concise snapshot for logs.
- **Testing**: YAML suites under `tests/rvm/vm/suites` exercise loops,
  comprehensions, virtual data, host awaits, and serialization. `complex.yaml`
  combines nested loops, comprehensions, function calls, and host awaits.

---


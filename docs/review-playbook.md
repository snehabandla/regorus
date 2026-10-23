# Review and Fix Playbook for Policy Evaluation Changes

This playbook distills lessons from the keyed partial-set review and fix cycle.
It is intended for authors, human reviewers, and AI-assisted development. The
examples come from that work; the process is reusable for compiler, interpreter,
VM, and binding changes.

The central lesson: **a plausible patch, a detailed review, and many passing
tests are different kinds of evidence. None substitutes for the others.**

## 1. What kept recurring

| Pattern | What happened | Reusable lesson |
|---|---|---|
| Fixing one syntax shape | Direct-variable keys worked; expression keys, multiple bindings, and nested loops exposed related gaps. | Define the semantic requirement first, then enumerate supported syntax forms that express it. |
| Fixing one execution surface | Parent evaluation could work while direct child lookup missed dynamic contributions. | Check every way the same value is reached, not only the path in the reproducer. |
| Filtering too late | A nonmatching rule evaluated a dependent expression first and reported false recursion. | A filter must dominate the work it is supposed to prevent. Trace execution order. |
| Filtering too early | Speculative key evaluation could run before a false guard or before required bindings existed. | Knowing an expression's inputs is not enough: early evaluation must also preserve errors, side effects, and control flow. |
| Confusing state lifetimes | Nested projections shared loop bindings; body-specific guard state could leak between bodies. | Give each cache, binding, and flag an explicit owner and lifetime. |
| Optimizing allocation too narrowly | Sizing an isolated cache only for the current module passed keyed tests but broke cross-module function calls. | Include module transitions and existing callers in the ownership model before narrowing storage. |
| Treating spelling as semantics | `lower` and `concat` were assumed to be safe builtins by name. | Resolve the actual target, including imports, user functions, extensions, and overrides. |
| Incomplete review intake | Some findings were in review-summary prose or issue comments, not inline threads. | Inventory every comment before declaring a review assessed. |
| Unverified reviewer claims | Some examples were parser-invalid; a scalar-collection error claim conflicted with existing behavior. | Treat every finding as a hypothesis, including findings from a verifier. |
| Treating a name as a fixed meaning | `input` was assumed always global, but Rego v0 bodies can shadow it locally. That surfaced in two consecutive review rounds. | List every implicit "always true" assumption an optimization relies on and look for counterexamples in each language version. |
| Explaining compatibility imprecisely | `#[non_exhaustive]` was initially discussed as though it removed the current break. | Separate compatibility now, migration cost, and protection against future changes. |

## 2. Begin with a complete review inventory

Read inline threads, the review summary, ordinary PR comments, and linked
reproducers or test proposals. Preserve each finding's identity across rounds;
do not renumber it informally as "the fourth one."

Maintain a small ledger in a working artifact or review comment:

| Field | Required content |
|---|---|
| Identity | Stable ID, review/comment reference, and short title |
| Claim | Expected behavior versus claimed actual behavior |
| Scope | Affected evaluator, VM mode, entrypoint, and input conditions |
| Evidence | Valid reproducer, source trace, or measurement |
| Status | Unassessed, reproduced, source-confirmed, fixed, already fixed, disproved, or unresolved |
| Resolution | Root cause, regression test, fix commit, and any remaining boundary |

Use precise dispositions:

- **Already fixed** does not mean the finding was never real.
- **Invalid reproducer** does not disprove the underlying concern.
- **Not reproduced** does not mean disproved.
- **Source-confirmed** is not the same as reproduced by execution.
- **Deferred** or **unresolved** must remain visible, not disappear from a summary.

## 3. Turn each claim into an executable contract

For a correctness finding, record:

```text
Policy:
Input/data:
Query or entrypoint:
Execution path and mode:
Expected value or error:
Actual value or error:
Why this difference matters:
```

First confirm the policy parses and reaches the intended code. In this work,
some direct call/arithmetic expressions in reference heads were rejected by the
parser. Equivalent body-bound keys were needed to investigate the concern.
Changing syntax can change scheduling, so document why the replacement tests
the same requirement.

Then construct a counterexample to the proposed fix. For example, after showing
that a nonmatching projection must not recurse, show that a matching recursive
projection still errors. A filter that simply hides all recursion is not a fix.

For performance claims, establish what the counter measures before optimizing.
Two callback calls might represent two distinct keys, not a repeated evaluation
of one key. An attempted processed-path fast path did not change the observed
counter and was removed rather than retained as an unproven optimization.

## 4. Review dependencies and lifetimes, not just functions

For evaluation-order changes, draw this dependency chain:

```text
collection readiness -> loop binding -> complete key readiness
                     -> projection match -> dependent body/value work
                     -> output accumulation
```

Check both sides of every scheduling decision:

- Too late: can irrelevant work recurse, allocate, invoke a callback, or fail?
- Too early: can a false guard no longer suppress an error or callback?
- Nested dependencies: can a later collection use an earlier loop binding?
- Final output: is the actual key checked before evaluating or accumulating its
  member, even when an early filter could not run?

For mutable state, write down:

```text
State | Owner | Lifetime | Cache key | Invalidation | Error-path restoration
```

In Regorus, useful distinctions include policy-wide metadata, one evaluation,
one rule invocation, one body, and one loop iteration. Review success, failure,
and nested invocation separately. Pay particular attention to `?`, early returns,
module switches, and paired push/pop or save/restore operations.

**State isolation and storage sizing are separate requirements.** An isolated
frame can still call into another module. The active-module-only cache sizing
optimization in this cycle caused existing imported-function and prepared-clone
tests to panic. It was replaced with capacity for all modules; the potential
allocation cost remains a future measurement/design task, not a solved
optimization.

## 5. Build a semantic test matrix

Use the matrix to choose cases, not to generate a full Cartesian product.
Every confirmed bug needs a minimal regression plus its nearest meaningful
counterexample.

| Dimension | Important partitions |
|---|---|
| Execution | Interpreter; RVM run-to-completion; RVM suspendable |
| Lookup | Parent; direct child; sibling; parent then child; child then parent |
| Key | Literal; input-derived; one local binding; multiple bindings; nested loops |
| Binding | Assignment; unification in either operand order; `some-in`; source-order changes |
| Match | Matching; nonmatching; missing/Undefined; multiple matching contributions |
| Body | True; false; Undefined; dependent expression before/after key binding |
| Calls | Actual builtin; user-defined shadow; extension; import; `with` replacement |
| State | Nested call; cross-module call; same-engine error then success; cloned engine |
| Resources | Growing keys/rules; repeated child reads; limits; copy-on-write behavior |

Additional rules:

- Assert exact values and error categories, not just "does not panic."
- Keep Undefined distinct from false and empty collections.
- Include both key iteration orders when shared state could make order matter.
- Do not infer coverage from the total number of YAML cases.
- Check which execution paths the test harness actually exercises.
- Keep parser restrictions explicit; do not claim unsupported syntax is covered.
- A proposed test matrix is not implemented coverage until cases exist and run.

## 6. Use independent review as a hypothesis generator

For high-risk evaluation changes, use the repository's `deep-review` process
before committing fixes:

1. Independent discovery: broad scan, concrete value-flow tracing, and
   safety/API/resource analysis.
2. Risk-triggered focused passes, including test adequacy when tests change.
3. Adversarial verification that attempts to disprove candidates and find gaps.
4. A report that distinguishes surviving findings, resolved findings, dropped
   claims, test gaps, and uncertainty.

Keep source-only review separate from execution-based validation. Give
reviewers the exact base and head, including whether uncommitted changes are in
scope. If code changes materially during review, identify what was reviewed
before and after the change.

Do not equate "three reviewers agree" with proof. In this cycle, the final
verifier reported that scalar head-loop collections should error, but existing
interpreter and RVM behavior supported no iteration. The claim needed disproof,
not an automatic code change.

Also do not overrule a concrete divergence with a general argument. A claim
about a named head-loop variable used in the body requires determining whether
the policy is supported and whether the change introduced the difference.
If that is not established, retain it as unresolved.

## 7. Validate beyond the new regression

Use a widening validation ladder:

1. Reproduce the original failure on the pre-fix implementation when practical.
2. Run the smallest regression covering the fix and its counterexample.
3. Run neighboring cases: imports, helper functions, clones, overrides, and
   recovery when the change touches shared evaluation state.
4. Run the repository's required broader checks before publication.
5. Let commit/push hooks run; investigate failures rather than bypassing them.

The keyed suite passed while two existing library tests still failed during
pre-push validation. That is direct evidence that feature-focused tests alone
were insufficient for a shared interpreter-state change.

Use the repository-compatible toolchain consistently, including nested hook
commands. During this work, Rust 1.95.0 was used; the environment's default
1.99.0 exposed unrelated lint/deprecation failures. Distinguish those failures
from diagnostics introduced by the patch, and fix the latter.

After a hook failure, check whether the commit or push actually happened before
retrying. Never claim publication from an attempted command.

## 8. Treat public API evolution as a deliberate decision

For a public enum:

- Adding a variant breaks downstream exhaustive matches.
- Adding `#[non_exhaustive]` to an already-public enum also breaks exhaustive
  matches, because downstream code must now include a wildcard arm.
- The attribute protects against future variant additions; it does not erase
  the current migration.
- Existing callers with suitable wildcard arms generally do not need changes
  for variant additions alone.

For this work, the chosen direction was to mark `Instruction` and `VmError`
non-exhaustive and explicitly communicate the break. Direct Rust RVM consumers
are the affected audience; this is not automatically a change to the C ABI or
the ordinary high-level engine calling convention.

Name the affected types, new variants, required migration, and release-policy
implication. Serialized instruction compatibility is a separate question;
Rust source compatibility does not establish wire-format compatibility.
Public code-search results also do not prove there are no private consumers.

## 9. Split and optimize by semantic boundary

Keep independently reproducible correctness fixes separate from new reporting,
partial evaluation, bindings, and demos. Each split should declare prerequisites
and build/test independently; splitting commits mechanically does not establish
those properties.

For default-off functionality, audit metadata, VM fields, instrumentation,
APIs, bindings, and CLI registration, not just the top-level module. Validate
disabled builds as well as enabled ones.

For implementation choices, compare a baseline and alternatives against the
same correctness corpus before selecting by size or speed. Measure compilation
and evaluation separately, plus allocations, retained memory, and scaling.
Parent-indexed lazy lookup avoided persistent per-child copies in this work;
that structural improvement alone is not a complete benchmark result.

## 10. Publication and handoff checklist

- [ ] Every review comment has a recorded disposition.
- [ ] Confirmed bugs have regressions and matching/nonmatching counterexamples.
- [ ] Shared-state changes cover nested and cross-module calls and recovery.
- [ ] The deep-review report reflects the code that will actually be committed.
- [ ] Broader validation is complete, or blockers are stated explicitly.
- [ ] Performance claims have measurements; abandoned experiments are removed.
- [ ] Public API and feature-gating decisions are explicit.
- [ ] The intended branch and PR destination are verified.
- [ ] Commit and remote head are verified after push.
- [ ] The PR comment explains fixes, remaining limitations, and breaking changes.

Suggested review response:

```text
Finding ID and title:
Disposition:
Root cause:
Change:
Regression and counterexample:
Validation scope:
Remaining limitation or compatibility impact:
Commit:
```

## 11. Minimize review round-trips

### Why rounds kept coming

The keyed-projection rounds followed one loop:

1. Fix the reported case.
2. The reviewer finds the next case.
3. Fix that case.

The root cause was structural. Early key filtering is an optimization that
must be invisible: it may skip work, but it must never change the answer.
Every rule that decides when filtering is safe (readiness, statement
reordering, loop hoisting) depends on unstated assumptions:

- `input` is global;
- a binding is never undone;
- every statement shape compiles the same way.

Each fix added or tightened one rule. A regression test for one repro proves
only that repro. The reviewer then found the next counterexample to the same
assumption:

| Round | Assumption broken |
|---|---|
| 3 | Bindings persist across backtracking. |
| 3 | Hoisted loops behave like ordinary statements. |
| 4 | `input` aliases are always global. |
| 5 | `input` is always global (direct head keys). |

### Process changes

1. **Write the invariant as an executable oracle.** For pruning optimizations,
   the optimized result must equal the unoptimized result. Encode that as a
   differential test over generated policies, not only hand-written repros.
   - Example: `tests/rvm/rego/keyed_projection_differential.rs`, which checks
     5 key forms × 14 statements in ordered pairs, plus v0 `input`-shadow
     bodies, across 5 inputs.
   - It compares projected `values.a` with the unprojected `values["a"]` on
     the interpreter and on both RVM modes.
   - Retroactively, it catches the round-5 bug (53 divergences at `30a7e81`),
     a round-3 bug (`SomeIn should have been hoisted`, at `ba74490`), and the
     original bug (372 divergences on `main`).
2. **Compare each engine with itself first.** Comparing the RVM with the
   interpreter mixes projection bugs with existing parity gaps. One example:
   the RVM treats `y := <undefined>` as success when `y` is unused. Check
   projection invariance per engine. Track cross-engine parity separately.
3. **Audit assumptions before pushing.** For each fix, list what the new code
   assumes to be always true, such as global names, binding lifetimes,
   statement shapes, language version, and `with` overrides. Try to break
   each assumption. Extend the generator with that dimension, not just one
   case.
4. **Be conservative by default.** If a pre-check cannot prove safety,
   skip the shortcut and let the final authoritative check decide. Losing
   pruning is a performance cost; a wrong prune is a correctness bug.
5. **Fix by class, in one push.** When a comment arrives, fix every member of
   its class:
   - Add the dimension to the differential generator.
   - Confirm the test fails on the pre-fix commit.
   - Then fix and push once.
6. **Run the generator against old commits.** A useful oracle fails on
   historical buggy revisions. If it does not, the generator is missing a
   dimension.
7. **Keep generator filters explicit.** Skip only invalid generated policies,
   and only by named error categories (`unsafe`, `used before definition`,
   `Undefined variable`). Never skip all errors.

## What to avoid next time

Do not declare all comments assessed after reading only inline threads. Do not
call an already-fixed finding "not real." Do not retain an optimization that
does not improve its reproducer. Do not claim no remaining issues when an
execution path is still unexplained. Do not describe a completed review pipeline
as a guarantee, or a passing focused suite as full validation.

The desired outcome is not fewer review comments at any cost. It is fewer
repeated root causes, better evidence for each decision, and an honest account
of what remains uncertain.

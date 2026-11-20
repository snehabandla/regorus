# Explanation and partial-evaluation corpus

A shared set of Rego policies and inputs for explanation (causality) and
partial-evaluation tests. The expected values come from Rego semantics and are
checked against OPA, so a test that adds explanation or residual expectations
can trust the value it explains.

The harness is `mod.rs`. It runs with the `rvm` feature:

```bash
cargo test --test mod explanation_corpus
# Also check every expected value against OPA:
REGORUS_OPA=/path/to/opa cargo test --test mod explanation_corpus::corpus_matches_opa
```

## Tests

- `corpus_values`: runs every example on the interpreter and on the RVM in both
  run-to-completion and suspendable modes. The outcome must equal `want_*`, or
  `divergence.actual_*` for the engines the divergence lists.
- `corpus_is_well_formed`: checks the structural rules below and prints how
  many cases cover each construct.
- `residual::corpus_partial_eval` (with `explanations`): removes each example's
  declared unknown subtrees, runs run-to-completion PE, checks its expected
  status and optional alternative count, then applies every Exact structured
  residual to the original concrete input and compares with `want_*`.
  It never uses an ordinary-evaluation divergence as the PE oracle.
- `corpus_matches_opa`: when `REGORUS_OPA` is set, runs `opa eval` for every
  example (except cases with `opa_skip`) and compares with `want_*`. Error
  messages differ between OPA and regorus, so any OPA evaluation error
  (`eval_*` code) satisfies `want_error`. A parse, compile or usage error from
  OPA fails the test. Without `REGORUS_OPA` this test does nothing.

## Format

Each `cases/*.yaml` file has a `cases` list. A case is one policy and query;
its examples are inputs to it.

```yaml
cases:
  - note: unique_snake_case_name
    description: What the case shows.
    constructs: [complete_rule, default]   # see `Construct` in mod.rs
    modules:
      - |
        package test
        default allow := false
        allow if input.role == "admin"
    query: data.test.allow
    data: {}                      # optional
    rego_v0: false                # optional; parse modules as Rego v0
    strict_builtin_errors: false  # optional; true makes builtin errors errors instead of Undefined
    unknowns: [input.role]        # required iff tagged unknown_input
    partial_eval: {status: unsupported} # required iff tagged unknown_input
    secrets: ["s3cr3t"]           # required iff tagged secret
    opa_skip: reason              # optional; OPA can't run this case
    examples:
      - note: admin
        input: {role: admin}      # absent means no input document
        want_result: true         # "#undefined" for Undefined, {"set!": [...]} for a set
      - note: guest
        input: {role: guest}
        want_result: false
```

An example sets exactly one of `want_result` or `want_error` (a substring of the
regorus error message). Error messages quote the failing source line, so the
substring must not occur in the policy itself.

### Rules checked by `corpus_is_well_formed`

- Notes, the query and every module are non-empty. Case notes are unique, and example notes
  are unique within a case.
- Each case has at least two distinct expected outcomes, so every matching
  example has a nonmatching twin.
- Every construct is covered by at least one case.
- `unknowns` is set exactly when the case is tagged `unknown_input`, and every
  path is under `input`. Dotted keys, JSON-quoted bracket keys and unsigned
  bracket indices are supported, preserving key/index identity. With
  `explanations`, the same typed-path decoder checks declaration syntax and
  residual lookup; other roots and dynamic paths are rejected.
- `partial_eval` is required exactly for `unknown_input` cases. Its `status`
  is `exact`, `unsupported`, `partial` or `possible_conflict`. Optional
  `alternatives` counts alternatives only for Exact cases; omit it when
  known facts give different counts across examples.
- `secrets` is set exactly when the case is tagged `secret`, and every secret
  appears in the case's input or data.
- A divergence's actual outcome differs from the expected one.
- No expected or actual error text occurs in the policy source.
- `explanation` is rejected until a checker exists.

### Divergences

When regorus disagrees with OPA, `want_*` stays the correct value and the
example records what regorus does today:

```yaml
        divergence:
          reason: Why regorus differs, with an upstream issue link if one exists.
          engines: [rvm]          # interpreter, rvm, or both
          actual_result: "#undefined"   # or actual_error: "substring"
```

Fixing the bug makes the test fail on the listed engines; remove the
divergence then.

## Partial-evaluation oracle

The original 19 unknown-input cases now all have explicit expectations:
`complete_rule_two_conditions` is Exact and the other 18 are Unsupported on
the reviewed B34 producer. New cases exercise general JSON values, typed paths,
numeric comparisons, known-gate elimination and all six deployment-context
leaves. Integration-branch reproductions keep their correct ordinary results
and explicitly Unsupported PE, rather than pinning defective exact answers.
The nested-negation chain uses six helper links, preserving the original
thirty-link chain's even polarity without exceeding default native-depth limits.
The original deep reproduction remains outside this completion oracle; resource
behavior is a separate gate in `tests/rvm/rego/cases/native_depth.yaml`.

`residual.rs` interprets structured residual fields after serializing the live
typed PE result. Concrete results retain their native `Value` so a concrete
set is not mistaken for its JSON array representation. Presentation `text`,
source locations, rule names and warnings are
never executable. Conditions in one alternative are AND; complete rules and
functions select the first matching ordered alternative (including defaults).
Partial sets collect and deduplicate every matching value; partial objects
collect keyed values and reject conflicting contributions. Empty partial
collections remain defined; absent complete results remain Undefined, not
false or null. Numeric comparisons use `regorus::Value` equality/ordering,
not floating-point coercion.

The deliberately small applier supports input-rooted existence, truthiness,
the six comparisons and recursively nested negation. It rejects non-Exact
outcomes, malformed alternatives, unknown rule/condition kinds, unsupported
operators (including `in` for now), calls and missing structured fields.
Validation covers even untaken alternatives. Future producers must extend
this checker alongside their supported constructs; it does not claim to
execute every representable contract kind. The current producer still does
not support unknown `data` declarations, context residuals, suspendable PE
or unknown collection iteration. There is no optional OPA residual-coverage
report; `corpus_matches_opa` checks concrete outcomes only.

Focused validation selectors (run by the build owner):

```bash
cargo +1.95.0 test --features explanations --test mod explanation_corpus
cargo +1.95.0 test --test mod explanation_corpus
REGORUS_OPA=/path/to/opa cargo +1.95.0 test --features explanations --test mod explanation_corpus::corpus_matches_opa
```

The test-only contract controls cover the #876 complete/set/object fixtures,
ordered fallback, wrong residual answers, unsupported semantics, required PE
fields, typed paths, null and precision beyond `f64`. They do not establish
that broader PE production is supported.

`explanation` remains reserved. A feature adding explanation expectations must
replace its type, add a producer check and fill supported examples.

New constructs get new cases with a twin.
Test functions for `cases/*.yaml` are generated at compile time, so after adding
a new file, rebuild the tests (for example, `touch tests/explanation_corpus/mod.rs`).

`unknowns` gives the input paths partial evaluation treats as unknown, and each
example's input is one concrete assignment of them. `secrets` lists values that
must not appear unredacted in a report.

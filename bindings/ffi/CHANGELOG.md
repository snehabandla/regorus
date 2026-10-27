# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed
- Panic containment no longer swaps the process-global panic hook on every call; concurrent calls could race on it. The first guarded call installs one hook that chains to the previous one and records the panic location for the returned message. Poison is set as soon as a panic is caught.
- `regorus_engine_test_trigger_panic` and `regorus_engine_test_reset_poison` are test-only and are exported only with the new `test-hooks` feature (the header guards them with `REGORUS_FFI_TEST_HOOKS`). Consumers that called them from a default build must build with `--features test-hooks`.
- The `explanations` feature now implies `rvm`, and `causality_msgpack` implies `explanations`.
- C#: `Rvm.TakeCausalityReportMsgpack` is renamed `Rvm.TakeCausalityReportMsgPack`.

## [0.1.0](https://github.com/microsoft/regorus/releases/tag/regorus-ffi-v0.1.0) - 2024-02-08

### Other
- C++ binding ([#129](https://github.com/microsoft/regorus/pull/129))
- Bindings for C, C#, Golang ([#124](https://github.com/microsoft/regorus/pull/124))

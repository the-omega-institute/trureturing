trureturing — the last line of the ledger is always the first line of the next round.

trureturing is a formal ledger for the golden-integer/Zeckendorf coordinate system, currently centered on D5, with Lean formalization and a separate machine-checkable .NET admission harness, StrataLint.

GitHub required-check configuration is a human gate and has not been verified by this repository.

StrataLint commands:

```text
Meta/StrataLint/lean-inspector/inspect.sh --repository ROOT --output REPORT
Meta/StrataLint check [--protected-base REV] --candidate-lean-report FILE --baseline-lean-report FILE
Meta/StrataLint coverage [--json]
Meta/StrataLint ledger-genesis --revision EXACT_COMMIT_OID
Meta/StrataLint route MANIFEST|-
Meta/StrataLint selftest
Meta/StrataLint topology
Meta/StrataLint worktree --branch NAME --path DIR [--base REV]
```

Lean inspection and .NET admission are separate programs. The inspector runs in
the pinned Lean environment and emits source-bound canonical JSON plus a SHA-256
sidecar; `check` consumes candidate and baseline reports without invoking Lean.

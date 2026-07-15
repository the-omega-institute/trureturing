# StrataLint.Cli Map

## Split history

- 2026-07-12 (SL-003): split the over-capacity CLI bucket by runtime responsibility.
  This was a local subdivision only; all C# namespaces remain `StrataLint.Cli`.

## Buckets

- `Admission/`: repository preparation, topology checks, and production admission.
- `Commands/`: command dispatch, coverage, registry loading, golden snapshot recording,
  ledger commands, and worktree provisioning.
- `Conservative/`: base-owned replay, TOML golden fixture execution/materialization,
  and conservative-extension verification.
- `Golden/`: shared conservative-corpus schema plus fail-closed canonical TOML
  loader/writer; case data remains outside the assembly under
  `Meta/StrataLint/Golden/cases` pending `RESIDENCE-EPOCH`.
- `Runtime/`: CLI adapters for precomputed Lean reports and pin-aware Lean cache provisioning.

The root contains the executable entry point, assembly metadata, SDK project metadata,
and this map.

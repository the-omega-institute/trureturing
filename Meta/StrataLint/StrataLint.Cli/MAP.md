# StrataLint.Cli Map

## Split history

- 2026-07-12 (SL-003): split the over-capacity CLI bucket by runtime responsibility.
  This was a local subdivision only; all C# namespaces remain `StrataLint.Cli`.
- 2026-07-28 (SL-003): split the two new papergen command files from `Commands/`
  when that bucket reached 14 files; existing command files remain in place and
  namespaces remain unchanged.

## Buckets

- `Admission/`: repository preparation, topology checks, and production admission.
- `Commands/`: command dispatch, coverage, registry loading, golden snapshot recording,
  ledger commands, and worktree provisioning; `Commands/Papergen/` holds paper recipe
  loading and validation.
- `Conservative/`: base-owned replay, TOML golden fixture execution/materialization,
  conservative-extension verification, and contract-epoch policy/plan/ledger/evidence
  obligation accounting from exact commit snapshots.
- `Golden/`: shared conservative-corpus schema plus fail-closed canonical TOML and
  synthetic-registry loaders/writer; data lives outside the assembly under top-level
  `Golden/` after closure of `RESIDENCE-EPOCH`.
- `Runtime/`: CLI adapters for precomputed Lean reports and pin-aware Lean cache provisioning.

The root contains the executable entry point, assembly metadata, SDK project metadata,
and this map.

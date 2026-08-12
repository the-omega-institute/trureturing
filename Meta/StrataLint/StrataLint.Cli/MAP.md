# StrataLint.Cli Map

## Split history

- 2026-07-12 (SL-003): split the over-capacity CLI bucket by runtime responsibility.
  This was a local subdivision only; all C# namespaces remain `StrataLint.Cli`.
- 2026-07-28 (SL-003): split the two new papergen command files from `Commands/`
  when that bucket reached 14 files; existing command files remain in place and
  namespaces remain unchanged.

## Buckets

- `Admission/`: repository preparation, topology checks, production admission, and the
  single-tree protected-surface content check used by the baseline gate.
- `Commands/`: command dispatch, coverage, registry loading, golden snapshot recording,
  ledger commands, and worktree provisioning.
- `Conservative/`: compatibility implementation for base-owned replay, TOML golden fixture
  execution/materialization, conservative-extension verification, and contract-epoch
  policy/plan/ledger/evidence obligation accounting from exact commit snapshots. It remains
  callable for predecessor baselines, but the current shared baseline gate does not invoke it.
- `Golden/`: shared compatibility schema plus fail-closed canonical TOML and
  synthetic-registry loaders/writer for the retained conservative commands; data lives
  outside the assembly under top-level `Golden/` after closure of `RESIDENCE-EPOCH`.
- `Runtime/`: CLI adapters for precomputed Lean reports and pin-aware Lean cache provisioning.

The root contains the executable entry point, assembly metadata, SDK project metadata,
and this map.

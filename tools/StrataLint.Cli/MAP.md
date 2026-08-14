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
- `Commands/`: command dispatch, coverage, registry and manifest loading, DAG ledger,
  digestion, file-map, blueprint-pin, and worktree commands.
- `GateAuthority/`: authority-root catalog loading and gate-authority verification.
- `Performance/`: performance event codecs, ledgers, reports, and budget comparison.
- `Runtime/`: CLI adapters for precomputed Lean reports, pin-aware Lean cache provisioning,
  Scribe emission verification, and worktree process execution.

The root contains the executable entry point, assembly metadata, SDK project metadata,
and this map.

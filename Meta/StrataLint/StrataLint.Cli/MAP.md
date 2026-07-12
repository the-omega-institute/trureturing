# StrataLint.Cli Map

## Split history

- 2026-07-12 (SL-003): split the over-capacity CLI bucket by runtime responsibility.
  This was a local subdivision only; all C# namespaces remain `StrataLint.Cli`.

## Buckets

- `Admission/`: repository preparation, topology checks, and production admission.
- `Commands/`: command dispatch inputs, registry loading, ledger commands, and worktree provisioning.
- `Runtime/`: bounded processes, Lean inspection, memoization, and Lean cache cloning.

The root contains the executable entry point, assembly metadata, SDK project metadata,
and this map.

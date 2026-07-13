# StrataLint.Tests Map

## Split history

- 2026-07-12 (SL-003): split the over-capacity test bucket by exercised domain.
  This was a local subdivision only; all C# namespaces remain `StrataLint.Tests`.

## Buckets

- `Admission/`: CLI outcomes, production admission, topology, and review regressions.
- `Commands/`: command parsing and end-to-end command behavior.
- `Coverage/`: applicability, UNGOVERNED, tower, ledger-state, and canonical coverage behavior.
- `Dag/`: truth DAG behavior.
- `Golden/`: current-engine executor and shape checks for the typed corpus owned by
  `StrataLint.Definitions`.
- `Ledger/`: frozen ledger, content address, revocation, and genesis behavior.
- `Rules/`: rule fixtures, registry, routing, and type-model behavior.
- `Runtime/`: snapshots, canonical raw Lean reports, and standalone Lean producer behavior.

The root contains shared global usings, SDK project metadata, and this map.

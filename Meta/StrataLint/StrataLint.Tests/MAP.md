# StrataLint.Tests Map

## Split history

- 2026-07-12 (SL-003): split the over-capacity test bucket by exercised domain.
  This was a local subdivision only; all C# namespaces remain `StrataLint.Tests`.

## Buckets

- `Admission/`: CLI outcomes, production admission, topology, and review regressions.
- `Dag/`: truth DAG behavior.
- `Golden/`: Python corpus and golden compatibility.
- `Ledger/`: frozen ledger, content address, revocation, and genesis behavior.
- `Rules/`: rule fixtures, registry, routing, and type-model behavior.
- `Runtime/`: snapshot and Lean process inspection behavior.

The root contains shared global usings, SDK project metadata, and this map.

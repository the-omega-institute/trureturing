# StrataLint.Tests Map

## Split history

- 2026-07-12 (SL-003): split the over-capacity test bucket by exercised domain.
  This was a local subdivision only; all C# namespaces remain `StrataLint.Tests`.
- 2026-07-16 (SL-003): split contract-epoch policy/schema/store/comparator tests from
  `Conservative/` when that bucket reached 13 files; namespaces remain unchanged.

## Buckets

- `Admission/`: CLI outcomes, production admission, topology, and review regressions.
- `Authorization/`: Hearts ledger format, append-only history, and exact SL-008 delta behavior.
- `Commands/`: command parsing and end-to-end command behavior.
- `Conservative/`: base-owned replay, policy roots, contract-epoch schemas/stores,
  obligation comparison, and conservative certificate behavior;
  `Conservative/ContractEpoch/` holds the focused contract-epoch suite.
- `Coverage/`: applicability, UNGOVERNED, tower, ledger-state, and canonical coverage behavior.
- `Dag/`: truth DAG behavior.
- `Golden/`: fail-closed loader fixtures, current-Engine snapshot checks, record-mode
  tests, and shape checks for canonical TOML case data.
- `Ledger/`: frozen ledger, content address, revocation, and genesis behavior.
- `Rules/`: rule fixtures, registry, routing, and type-model behavior.
- `Runtime/`: snapshots, canonical raw Lean reports, and standalone Lean producer behavior.

The root contains shared global usings, SDK project metadata, and this map.

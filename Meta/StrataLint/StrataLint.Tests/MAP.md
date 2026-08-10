# StrataLint.Tests Map

## Split history

- 2026-07-12 (SL-003): split the over-capacity test bucket by exercised domain.
  This was a local subdivision only; all C# namespaces remain `StrataLint.Tests`.
- 2026-07-16 (SL-003): split contract-epoch policy/schema/store/comparator tests from
  `Conservative/` when that bucket reached 13 files; namespaces remain unchanged.
- 2026-07-23 (SL-003): split the WM structural-drift matrix from
  `TheoryAtomizerTests.cs` after the fail-closed regression suite reached the file ceiling.
- 2026-07-24 (SL-003): split the five new PR shepherd recalculation test parts from
  `Commands/`; existing command tests remain in place and namespaces remain unchanged.
- 2026-07-28 (SL-003): split the new papergen command suite from `Commands/` when
  that bucket reached 13 files; existing command tests remain in place and namespaces
  remain unchanged.
- 2026-08-03 (SL-003): split `Commands/Papergen/PapergenCommandTests.cs` into loader tests,
  membership tests and the carrier fixture once frozen-ledger membership coverage pushed it
  past the 800-line artifact ceiling. Declared `partial` rather than moving helpers, so the
  fixture stays a single source and no visibility changed; namespaces remain unchanged.

## Buckets

- `Admission/`: CLI outcomes, production admission, topology, and review regressions.
- `Authorization/`: Hearts ledger format, append-only history, and exact SL-008 delta behavior.
- `Commands/`: command parsing and end-to-end command behavior;
  `Commands/Papergen/` holds paper recipe validation and
  `Commands/PrOpenScriptTests.cs` holds the focused one-shot PR open/update script contract.
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

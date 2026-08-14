# StrataLint.Tests Map

## Split history

- 2026-07-12 (SL-003): split the over-capacity test bucket by exercised domain.
  This was a local subdivision only; all C# namespaces remain `StrataLint.Tests`.
- 2026-07-16 (SL-003): split the then-existing contract-epoch tests from the
  conservative bucket; both directories have since retired and namespaces remain unchanged.
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

- `Admission/`: CLI outcomes, production admission, topology, review regressions, and the
  current single-tree protected-surface gate contract.
- `Authorization/`: Hearts ledger format, append-only history, and exact SL-008 delta behavior.
- `BlueprintPins/`: blueprint pin parsing and validation.
- `Commands/`: command parsing and end-to-end command behavior;
  `Commands/PrOpenScriptTests.cs` holds the focused one-shot PR open/update script contract.
- `Coverage/`: applicability, UNGOVERNED, tower, ledger-state, and canonical coverage behavior.
- `Dag/`: truth DAG behavior.
- `Digestion/`: atomization, alignment, ledger, formalization, and ingestion behavior.
- `Fixtures/`: shared declarative test fixture data.
- `FrozenLedger/`: frozen ledger transitions, content addresses, and git adapters.
- `Ledger/`: ledger append and reattest commands plus their production fixture.
- `Performance/`: performance event, budget, command, and ledger behavior.
- `Revocation/`: revocation records and suffix validation.
- `Rules/`: rule fixtures, registry, routing, and type-model behavior.
- `Runtime/`: snapshots, canonical raw Lean reports, and standalone Lean producer behavior.

The root contains shared global usings, SDK project metadata, and this map.

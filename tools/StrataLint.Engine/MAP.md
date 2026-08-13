# StrataLint.Engine Map

## Split history

- 2026-07-12 (SL-003): split the over-capacity engine bucket by cohesive domain.
  This was a local subdivision only; all C# namespaces remain `StrataLint.Engine`.
- 2026-07-12 (SL-003): split semantic path parsing from `RepositoryPathPolicy.cs`
  into a same-namespace partial source after the file crossed 400 lines.
- 2026-07-22 (SL-003): split the Observer theory dialect adapter from
  `TheoryAtomizers.cs` after the shared atomizer source reached the file ceiling.
- 2026-07-23 (SL-003): split WM structural validation into `Digestion/Wm/`
  after its fail-closed regression fix brought `TheoryAtomizers.cs` to the file ceiling.

## Buckets

- `Admission/`: admission capabilities, declarative bootstrap protection policy and
  gating, Lean validation, and profiles.
- `Authorization/`: the canonical Hearts authorization ledger parser and append-only reader.
- `Coordinates/`: repository coordinates, registry policy, routing, and target syntax.
- `Coverage/`: harness coverage models, tower validation, ledger indexing, and canonical reports.
- `Dag/`: truth DAG models and construction.
- `Digestion/`: theory atomization, fingerprint subtraction, typed receipts, and status derivation.
- `Ledger/`: frozen content and ledger mechanics; `Validation/` holds validation phases.
- `Revocation/`: revocation planning and trusted receipts.
- `Rules/`: rule catalog, execution, repository rule implementations, and the shared BACKFILL loader.
- `Runtime/`: bounded processes, Git working-tree snapshots, and precomputed report adapters.
- `Snapshot/`: repository snapshots, canonical writers, and the source-bound raw Lean report contract.

The root contains only assembly and SDK project metadata plus this map.

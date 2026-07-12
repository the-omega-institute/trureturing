# StrataLint.Engine Map

## Split history

- 2026-07-12 (SL-003): split the over-capacity engine bucket by cohesive domain.
  This was a local subdivision only; all C# namespaces remain `StrataLint.Engine`.

## Buckets

- `Admission/`: admission capabilities, bootstrap gating, Lean validation, and profiles.
- `Coordinates/`: repository coordinates, registry policy, routing, and target syntax.
- `Coverage/`: harness coverage models, tower validation, ledger indexing, and canonical reports.
- `Dag/`: truth DAG models and construction.
- `Ledger/`: frozen content and ledger mechanics; `Validation/` holds validation phases.
- `Revocation/`: revocation planning and trusted receipts.
- `Rules/`: rule catalog, execution, and repository rule implementations.
- `Snapshot/`: repository snapshots and canonical writers.

The root contains only assembly and SDK project metadata plus this map.

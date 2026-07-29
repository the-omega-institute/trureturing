# D5 S1 Map

## Split history

- 2026-07-27 (SL-003): `Digit/` reached 13 Lean files when the WM L3b' unit
  added `CompositeGasOrder.lean`. The branch-new module opened the `Quad/`
  bucket; all 12 paths already present in `origin/dev` remain in place.

## Buckets

- `Depth/`: finite-resolution depth combining scale, support size, and phase.
- `Digit/`: raw and canonical W-digit representations and carry rules.
- `Phase/`: additive golden-ratio phases modulo one.
- `Quad/`: parameterized quadratic presentation rings and actual orders
  carrying the digit-gas root-unit criteria.
- `Scale/`: real embeddings and logarithmic scales of golden integers.

- 2026-07-30 SL-003 分裂记录:Digit 桶达 12 上限;按"只裂不迁"新增子疆域桶 `Deficit/`(组名已入词表),存量 Digit 模块地址全数保留;首件 `Deficit/DeficitInteger.lean`。

- 2026-07-30 SL-003 分裂记录:Blueprint/D5/S1/Phase 达 12 上限(6 文档 ×2 件);按"只裂不迁"新增子疆域桶 `Dynamics/`(组名已入词表),存量 Phase 模块地址全数保留;首件 `Dynamics/JumpCocycle.lean`。

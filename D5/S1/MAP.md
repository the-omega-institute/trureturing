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
- `Solenoid/`: compact solenoid models and hidden-fiber constructions.
- `Words/Complexity/`: general finite-alphabet factor-complexity theorems.
- `Words/ReturnWords/`: return blocks between adjacent occurrences of golden factors.

- 2026-07-30 SL-003 分裂记录:Digit 桶达 12 上限;按"只裂不迁"新增子疆域桶 `Deficit/`(组名已入词表),存量 Digit 模块地址全数保留;首件 `Deficit/DeficitInteger.lean`。

- 2026-07-30 SL-003 分裂记录:Blueprint/D5/S1/Phase 达 12 上限(6 文档 ×2 件);按"只裂不迁"新增子疆域桶 `Dynamics/`(组名已入词表),存量 Phase 模块地址全数保留;首件 `Dynamics/JumpCocycle.lean`。
- 2026-07-30 SL-003 分裂记录:Blueprint/D5/S1/Phase 达 12 上限;按"只裂不迁"新增子疆域桶 `Words/`(组名已入词表),存量 Phase 模块地址全数保留;首件 `Words/GoldenMechanicalWord.lean`。
- 2026-08-04 SL-003 分裂记录:Dynamics 桶达 12/12 饱和触发 SL-003;按"只裂不迁"新增子疆域桶 `Solenoid/`(组名已入词表),既有 Dynamics 路径零移动;首件 `Solenoid/HiddenFiberCompact.lean`。
- 2026-08-11 SL-003 split record: `Words/` reached its 12-Lean-file limit;
  opened the local subdomain `Words/ReturnWords/` under the route engine's one-level
  split rule. Existing Words paths remain unmoved, Lean namespaces remain
  `D5.S1.Words`, and the first module is `ReturnWords/GoldenReturnWords.lean`.
- 2026-08-12 SL-003 split record: `Words/` remained at its 12-Lean-file limit;
  opened the local subdomain `Words/Palindromes/` under the route engine's one-level
  split rule. Existing Words paths remain unmoved, Lean namespaces remain
  `D5.S1.Words`, and the first module is `Palindromes/GoldenPalindromicPrefix.lean`.
- 2026-08-13 SL-003 split record: `Words/` remained at its 12-Lean-file limit;
  opened the local subdomain `Words/Complexity/` for generic word-combinatorics
  theorems. Existing Words paths remain unmoved, and the first module is
  `Complexity/MorseHedlund.lean`.
- 2026-08-11 SL-003 split record: `Blueprint/D5/S1/Phase/` was already at its
  12-file limit; opened the local subdomain `Phase/Interference/` under the route
  engine's one-level split rule. Existing Phase paths remain unmoved, and the first
  module is `Interference/DominantPartialQuotientGap.lean`.
- 2026-08-12 SL-003 continuation: `Phase/Interference/` remains the recorded
  one-level host for additive countershot certificates; `M1728Countershot.lean`
  is appended there without moving existing paths.

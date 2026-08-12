# D5 S3 Map

## Split history

- 2026-07-18 (SL-003): `Weil/` reached 13 Lean files when batch-9 added
  `ZeroGeometry.lean`. The branch-new module opened the `Zeros/` bucket; all 12
  paths already present in `origin/dev` remain in place.
- 2026-08-01 (SL-003): `Blueprint/D5/S3/Arith` was at its 12-file limit.
  The branch-new `SumTwoSquares` module opened the `PrimeForms/` bucket; all
  existing `Arith/` paths remain in place.

- 2026-08-12 (SL-003): `Quantum/` was at its 12-file limit. The branch-new
  `CovariantCommutator` module opened the `Quantum/Algebra/` bucket; all 12
  existing `Quantum/` paths remain in place.
- 2026-08-12 (SL-003): `Observer/` was at its 12-file limit. The branch-new
  `ContinuousRigidity` module opened the `Observer/HiddenFlow/` bucket; all 12
  existing `Observer/` paths remain in place.
- 2026-08-12 (SL-003): `Observer/` remained at its 12-file limit. The
  branch-new `WindowGeneration` module opened the `Observer/WindowAlgebra/`
  bucket; all 12 existing `Observer/` paths remain in place.
- 2026-08-12 (SL-003): `Entropy/` was at its 12-file limit. The branch-new
  `CapacityMonotone` module opened the `Entropy/Forgetting/` bucket; all 12
  existing `Entropy/` paths remain in place.

## Buckets

- `Constants/`: canonical real constants and registered reference centers.
- `Fourier/`: entire extensions of the Weil Fourier-Laplace transform.
- `Quantum/`: finite-dimensional operator-algebra and probability structures.
- `PrimeForms/`: representations of prime numbers by integral quadratic forms.
- `Weil/`: classical zeta conventions, test functions, and explicit-formula machinery.
- `Zeros/`: zeta-zero geometry, symmetry, and local critical-line balance.
- 2026-08-04 SL-003 分裂记录:Blueprint/D5/S3/Arith 达 12 上限;按"只裂不迁"新增子疆域桶 `Axis/`(组名已入词表),存量 Arith 模块地址全数保留;首件 `Axis/PrimeAxisEscape.lean`。
- 2026-08-10 SL-003 分裂记录:D5/S3/Arith 达 12 上限;按"只裂不迁"新增子疆域桶 `Factorization/`(组名已入词表),存量 Arith 模块地址全数保留;首件 `Factorization/FreeCommMonoid.lean`。
- `Quantum/Algebra/`: representation-independent covariance and commutator algebra.
- `Observer/HiddenFlow/`: continuous hidden-parameter flow exclusion over discrete addresses.
- `Observer/WindowAlgebra/`: finite read-write generation of window matrix algebras.
- `Entropy/Forgetting/`: finite entropy and uniform-capacity laws under forgetting channels.

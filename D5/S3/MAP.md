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
- 2026-08-12 (SL-003): `Observer/` remained at its 12-file limit. The
  branch-new `OrbitConnesDistance` module opened the `Observer/MetricGeometry/`
  bucket; all 12 existing `Observer/` paths remain in place.
- 2026-08-12 (SL-003): `Entropy/` was at its 12-file limit. The branch-new
  `CapacityMonotone` module opened the `Entropy/Forgetting/` bucket; all 12
  existing `Entropy/` paths remain in place.
- 2026-08-13 (SL-003): `Zeros/` was at its 12-Lean-file limit. The split-only,
  no-move change opened `Zeros/Endpoints/`; all existing `Zeros/` paths remain
  unmoved. First module: `Endpoints/XiEndpointValues.lean`, an addressable
  certificate for the pole-removed xi reading's endpoint values.
- 2026-08-14 (SL-003): `Zeros/` remained at its 12-Lean-file limit. The
  split-only, no-move change opened `Zeros/Symmetry/`; all existing `Zeros/`
  paths remain unmoved. First module: `Symmetry/ZetaConjugationCovariance.lean`,
  proving conjugation and conjugate-reflection covariance for zeta readings.
- 2026-08-14 (SL-003): `Weil/` was at its 12-Lean-file limit. The split-only,
  no-move change opened `Weil/PrimeAddress/`; all existing `Weil/` paths remain
  unmoved. First module: `PrimeAddress/PrimeAddress.lean`, connecting finite
  Euler modifications, zero amplitudes, ramified silence, and prime readings.
- 2026-08-14 (SL-003): `Zeros/` remained at its 12-Lean-file limit. The
  split-only, no-move change opened `Zeros/Detection/`; all existing `Zeros/`
  paths remain unmoved. First module: `Detection/DetectionRadiusCertificate.lean`,
  certifying the exact visibility scale and radius at beta = 0.51 and gamma = 10^12.
- 2026-08-14 (SL-003): `Weil/` remained at its 12-Lean-file limit. The A17.2
  Zeta23 explicit-formula port opened cohesive `Weil/Zeta*` subdomain buckets;
  all existing `Weil/` paths remain unmoved. The port retains its upstream
  import order, and over-800-line sources are split only at declaration bounds.

## Buckets

- `Constants/`: canonical real constants and registered reference centers.
- `Fourier/`: entire extensions of the Weil Fourier-Laplace transform.
- `Quantum/`: finite-dimensional operator-algebra and probability structures.
- `PrimeForms/`: representations of prime numbers by integral quadratic forms.
- `Weil/`: classical zeta conventions, test functions, and explicit-formula machinery.
- `Weil/PrimeAddress/`: finite prime modifications, ramified-character silence, and prime-address amplitudes.
- `Weil/ZetaCore/`: Zeta23 definitions and explicit-formula convention dictionaries.
- `Weil/ZetaSeam/`: the hypothesis-free nontrivial-zeta-zero configuration.
- `Weil/ZetaLinear/`: finite-dimensional positive-index linear algebra used by the tail bounds.
- `Weil/ZetaGamma/`: gamma-factor series, Stirling estimates, and vertical bounds.
- `Weil/ZetaAnalytic/`: rectangle logarithmic-derivative integration.
- `Weil/ZetaPntBase/`: Apache-2.0 PrimeNumberTheoremAnd-derived analytic foundations.
- `Weil/ZetaPntBounds/`: the split zeta and logarithmic-derivative bound chain.
- `Weil/ZetaRvm/`: Riemann-von Mangoldt and local zero-count bounds.
- `Weil/ZetaTail/`: zero-sum tail and rank-one bounds.
- `Weil/ZetaExplicit/`: contour assembly of the hypothesis-free Weil explicit formula.
- `Zeros/`: zeta-zero geometry, symmetry, and local critical-line balance.
- `Zeros/Endpoints/`: endpoint-value certificates for completed-zeta readings.
- `Zeros/Symmetry/`: conjugation and reflection covariance of zeta readings.
- `Zeros/Detection/`: exact arithmetic certificates for zero-detection scales.
- 2026-08-04 SL-003 分裂记录:Blueprint/D5/S3/Arith 达 12 上限;按"只裂不迁"新增子疆域桶 `Axis/`(组名已入词表),存量 Arith 模块地址全数保留;首件 `Axis/PrimeAxisEscape.lean`。
- 2026-08-10 SL-003 分裂记录:D5/S3/Arith 达 12 上限;按"只裂不迁"新增子疆域桶 `Factorization/`(组名已入词表),存量 Arith 模块地址全数保留;首件 `Factorization/FreeCommMonoid.lean`。
- `Quantum/Algebra/`: representation-independent covariance and commutator algebra.
- `Observer/HiddenFlow/`: continuous hidden-parameter flow exclusion over discrete addresses.
- `Observer/WindowAlgebra/`: finite read-write generation of window matrix algebras.
- `Observer/MetricGeometry/`: observable-supremum metrics on observer update orbits, including
  `VisiblePhaseInfinity.lean` for the ENNReal visible-phase infinity shadow.
- `Entropy/Forgetting/`: finite entropy and uniform-capacity laws under forgetting channels.
- 2026-08-13 SL-003 分裂记录:D5/S3/Zeros 达 12 上限;按"只裂不迁"新增子疆域桶 `Zeros/ToySpectrum/`,存量 Zeros 模块地址全数保留;首件 `ToySpectrum/OffLineToySpectrum.lean`。
- `Zeros/ToySpectrum/`: explicit finite toy zero-spectra separating set-level symmetry from critical-line containment.

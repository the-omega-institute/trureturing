# Actual normal overlap maxima, finite positive-secant compatibility, and simultaneous whole-complex-L1 standard-predual realization on arbitrary concrete von Neumann algebras

## Abstract

Actual normal overlap maxima, finite positive-secant compatibility, and simultaneous whole-complex-L1 standard-predual realization on arbitrary concrete von Neumann algebras.

**Definition 1.1 (Positive functionals).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.Positive`

*Formalization.* `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.Positive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positivity is evaluated on every positive element of the actual C-star algebra, using the complex partial order. It is not positivity of a scalar mass alone.

**Definition 1.2 (Functional domination).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.Below`

*Formalization.* `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.Below` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Below phi psi means phi(a)<=psi(a) for every positive a. The secant chain uses this actual functional order.

**Definition 1.3 (Continuous overlap observation).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlapFunction`

*Formalization.* `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlapFunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous complex-valued function on the closed interval is x maps to min(x,t(1-x)). Both source axes are present.

**Definition 1.4 (Actual functional overlap).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlap`

*Formalization.* `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the reconstructed complex-linear map of the actual full moment family to overlapFunction t. The result is an actual continuous functional on the original algebra.

**Theorem 1.5 (Feasible posterior overlaps).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlap_feasible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlap_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t>=0 every posterior overlap is positive, below rho, and below t sigma in functional order. The proof applies positivity of the actual family to the pointwise observation inequalities.

**Definition 1.6 (Actual functional secants).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlapSecant`

*Formalization.* `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlapSecant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The functional divided difference is (t-s)^(-1) times (overlap(F,t)-overlap(F,s)). Its nonnegativity, upper bound by sigma, and antitonicity on separated intervals follow by applying the actual positive moment map to scalar secants. Mathlib concave slope monotonicity supplies the order reversal.

**Theorem 1.7 (Three-block realization).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.feasible_overlap_realized`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.feasible_overlap_realized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every t>0 and every actual positive eta dominated by rho and t sigma, construct a Family rho sigma whose overlap at t is exactly eta. The positive blocks are sigma-eta/t, rho-eta, and eta/t. They are placed at 0, 1, and t/(1+t), respectively, with middle coefficient 1+t. No state or division by the mass of a functional is chosen. Zero blocks remain harmless.

**Theorem 1.8 (Finite positive-secant interpolation).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.finite_positive_secants_realized`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.finite_positive_secants_realized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every strictly increasing finite knot tuple beginning at zero, take actual functional values X and decreasing slopes d with last slope zero, d(0)<=sigma, X(last)<=rho, and exact consecutive moment increments. Differences G_i=d_i-d_(i+1) are positive. Summation by parts gives sum G_i=d_0, sum t_i G_i=X(last), and sum min(t_j,t_i)G_i=X_j. The resulting genuine positive complex-linear moment map has both exact moments and every prescribed functional overlap. No finite-dimensionality, state normalization, or common optimizer premise occurs.

**Theorem 1.9 (Attained actual normal overlap maximum).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.normal_overlap_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.normal_overlap_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary concrete VonNeumannAlgebra H and arbitrary positive coefficient-series rho,sigma, maximize the continuous overlap mass coordinate on the actual compact full moment family. The three-block realization compares this maximum with EVERY feasible positive functional. Positive heredity from rho proves the maximizing overlap belongs to the independently defined coefficient-series predual. An optimizer is obtained, never assumed.

**Definition 1.10 (Actual standard-predual feasible masses).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.feasibleMasses`

*Formalization.* `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.feasibleMasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The set explicitly quantifies a continuous functional eta having an actual square-summable coefficient-series representation, positivity, both functional domination inequalities, and its real mass. No abstract scalar optimum is input.

**Definition 1.11 (The attained normal overlap value).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlapValue`

*Formalization.* `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlapValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real supremum of feasibleMasses is defined independently of any optimizer selection. normal_overlap_maximum and value_attained establish its actual maximum and a realizing posterior family for every positive threshold.

**Theorem 1.12 (The supremum is a genuine maximum).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.value_attained`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.value_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual normal overlap maximum is the conditional supremum of the nonempty bounded real feasible-mass set. Its family attains the value and every feasible positive functional has mass at most that value. This is consumed by the curvature-cost comparison.

**Definition 1.13 (Finite compatibility on arbitrary threshold sets).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.FiniteCompatibility`

*Formalization.* `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.FiniteCompatibility` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For EVERY finite increasing tuple t starting at zero with positive knots in K, there exist actual coefficient-series positive functional optimizers X_j. Their computed divided differences D_j are positive, bounded above by sigma, and antitone in functional order. X_0=0. Empty K and the empty positive knot tuple remain included. There is no unique-optimizer assumption.

**Theorem 1.14 (A single whole-L1 standard test).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.finite_compatibility_simultaneous_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.finite_compatibility_simultaneous_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FiniteCompatibility on ANY set K of positive thresholds implies one actual compact-family point attaining overlapValue at every t in K. Closed optimal-coordinate fibers have the finite intersection property by the actual functional interpolation theorem. Compactness gives one point without any countability restriction. The merged standard_posterior_realization constructs an actual complex-linear map on the ENTIRE L1 of its finite regular interval measure, with positive outputs, all complex masses, both exact moments, standard coefficient-series outputs, and every K-overlap optimum. This theorem alone asserts no f-cost equality.

**Theorem 1.15 (Exact finite-to-global overlap equivalence).**

Lean statement: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.finite_compatibility_iff_simultaneous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.finite_compatibility_iff_simultaneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FiniteCompatibility is equivalent to one actual posterior family simultaneously maximizing the actual normal overlap at every t in K. Necessity takes its actual functional overlaps and uses positive decreasing scalar secants through the positive moment map. Sufficiency uses the finite block construction and compact finite intersection argument. No curvature, finite cost, full-support, matrix, trace, faithfulness, normalization, separability, or spectral-optimality hypothesis is inserted.

Hiai--Mosonyi--Tomamichel, Hockey stick f-divergences, arXiv:2607.08760v1, supplies the original reverse-test and curvature framework and leaves the maximal-hockey equality classification open on PDF p. 62. The functional-analytic and scalar curvature ingredients are established antecedents. The separate full-support localized-centralizer theorem is outside this statement; worldwide priority remains unresolved.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.Below`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.FiniteCompatibility`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.Positive`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.feasibleMasses`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.feasible_overlap_realized`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.finite_compatibility_iff_simultaneous`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.finite_compatibility_simultaneous_realization`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.finite_positive_secants_realized`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.normal_overlap_maximum`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlap`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlapFunction`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlapSecant`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlapValue`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.overlap_feasible`
- Truth anchor: `D5/S3/Quantum/Divergence/NormalOverlapCompatibility.value_attained`
- Dependency: [D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment](GeneralConvexReverseTestAttainment.md)

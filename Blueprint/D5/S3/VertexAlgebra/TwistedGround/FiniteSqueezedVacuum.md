# Finite squeezed vacuum

## Abstract

The native finite bilinear Gaussian occupation vacuum and its normalized trace-log exponential.

Let I be any finite mode type, including the empty type. Let A and B be complex symmetric matrices on I, each with Euclidean continuous-linear-map norm strictly less than one. Symmetry means transpose symmetry, not Hermitian symmetry. All pairings are complex bilinear and contain no conjugation. No commutativity, positivity, diagonalizability, fixed occupation cutoff, nonzero vacuum premise or desired determinant formula is assumed.

The Gaussian/Bargmann-Wick squeezed-vacuum identity is classical. The native coefficient h_A(d) is FactorialFockQuadraticEstimate.gaussianCoefficient: the coefficient at d of Q_A^(degree(d)/2)/(degree(d)/2)!, where Q_A=(1/2) sum_ij A_ij X_i X_j. The factorial weight is FactorialFockMetric.weight(d)=product_i d_i!. This module constructs the analytic occupation argument for those existing coefficients. It claims no mathematical novelty and assumes no external Gaussian integral or determinant identity.

For every natural k, sum_d (degree(d)+1)^k weight(d) |h_A(d)|^2 is summable. Choose c>1 with c times the Euclidean operator norm of A less than one. Exact coefficient homogeneity gives h_(cA)(d)=c^(degree(d)/2)h_A(d), and odd occupations vanish. Mathlib's summability of a polynomial times a geometric progression supplies a finite domination constant. The existing occupation_summable theorem is applied directly to cA.

For every occupation alpha, sum_d |weight(d+alpha) h_A(d) h_B(d+alpha)| converges. The proof bounds the exact factorial ratio by a fixed polynomial in degree(d), uses polynomial occupation domination, and uses injectivity of the shift d maps to d+alpha. The full infinite occupation type remains in scope.

**Definition 1.1 (Original creation shift).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The creation monomial alpha shifts an occupation coefficient down by alpha, with zero when alpha is not bounded by that occupation.

**Definition 1.2 (Original bilinear factorial pairing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pairing of coefficient functions f and g is the unconditional sum over all shared occupations n of weight(n) f(n) g(n), without conjugation.

**Definition 1.3 (Original annihilation coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.annihilate`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.annihilate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At occupation d, annihilation in mode i is (d_i+1) times the coefficient at d+e_i.

**Theorem 1.4 (Composition of original creation shifts).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_add`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two creation shifts compose to their occupation sum, with the original zero-boundary convention.

**Theorem 1.5 (Zero creation shift).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Creation by the zero occupation is the identity on coefficient functions.

**Theorem 1.6 (Single-mode creation boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Creation in a single mode is zero at zero occupation and otherwise lowers that coordinate once.

**Theorem 1.7 (Shifted native Gaussian square estimate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_square_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_square_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every creation monomial alpha and symmetric strict Euclidean contraction A, sum_d weight(d) |created(alpha,gaussianCoefficient(A),d)|^2 converges. This is the original shifted occupation estimate and is consumed by the finite polynomial Gaussian row bridge.

**Theorem 1.8 (Scalar action of a creation shift).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_const`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A creation shift preserves scalar multiplication of coefficient functions.

**Theorem 1.9 (Finite sums under a creation shift).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original shift distributes over a finite sum indexed by the shared modes.

**Theorem 1.10 (Native two-sided created pairing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_pair_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_pair_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original two-sided Gaussian creation pairing is summable under only the two shared symmetric strict contractions.

**Theorem 1.11 (Symmetry of the bilinear occupation pairing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_comm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two coefficient functions may be exchanged in the original complex bilinear pairing.

**Theorem 1.12 (Exact factorial adjointness).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_creation_annihilation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_creation_annihilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Single creation on the first argument equals single annihilation on the second argument, by the original occupation reindexing and coordinate factorial identity.

**Theorem 1.13 (Actual Gaussian annihilation equation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.gaussian_annihilate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.gaussian_annihilate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite complex symmetric A, including empty mode types, annihilation in mode i of the actual gaussianCoefficient(A) equals the finite sum over j of A_ij times single creation in mode j of that same coefficient function. No analytic norm hypothesis is used. This reuses the original native polynomial coefficient recurrence.

**Theorem 1.14 (Scalar action in the original pairing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_const_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_const_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A scalar factor on the second coefficient function factors out of the unconditional complex sum.

**Theorem 1.15 (Finite sum exchange in the original pairing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_sum_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_sum_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite shared-mode sum may be exchanged with the occupation sum when every summand pairing is summable.

**Definition 1.16 (Actual bilinear creation insertion).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.insertion`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.insertion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The insertion at alpha is the unconditional sum over d of weight(d+alpha) h_A(d) h_B(d+alpha). At alpha zero this is the vacuum occupation pairing.

Fix S>1 such that S A is still a strict Euclidean contraction. For every complex t with |t|<S, the insertion with only A scaled by t is differentiable, and its derivative is the sum of the polynomial coefficient derivatives. An even occupation of degree 2n contributes n t^(n-1) h_A(d); its derivative at zero is taken as a polynomial derivative. Coefficient norms are uniformly dominated by the summable insertion norms at S A. A uniform summable derivative majorant uses polynomially weighted squared coefficients of S A and shifted squared coefficients of B. There is no division by t or a claimed finite supremum of n/R.

Writing Z=insertion(A,B,0) and N_ij=insertion(A,B,e_i+e_j), the exact identity is N_ij=B_ij Z+sum_kl B_ik A_kl N_jl. Creation and annihilation are adjoint for the bilinear factorial pairing. The shift d maps to d+e_i is an equivalence onto occupations with positive i entry; the boundary contribution vanishes there. Gaussian annihilation is taken from the public native polynomial coefficient recurrence, and the commutator produces its exact Kronecker delta. Absolute summability justifies finite-sum exchanges.

**Definition 1.17 (Normalized trace-log antiderivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.vacuumTraceLog`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.vacuumTraceLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At complex t, this is one half of sum over n>=0 of t^(n+1) trace((A B)^(n+1))/(n+1). It is zero at t=0. On a sufficiently small complex ball containing [0,1], its convergence and derivative follow from norm domination and the Neumann geometric series, including empty mode types.

**Theorem 1.18 (Actual vacuum trace-log identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.vacuum_trace_log`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.vacuum_trace_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupation series is absolutely summable, the trace series is summable, and the unconditional sum over all occupations of weight(d) h_A(d) h_B(d) equals exp((1/2) sum_(n>=0) trace((A B)^(n+1))/(n+1)). Only A_t=t A is scaled. The second moment solves N=(I-t B A)^(-1) B Z, and the vacuum satisfies Z'=trace(A (I-t B A)^(-1) B) Z/2 with Z(0)=1. Multiplying by the exponential of the negative trace-log gives a function with zero derivative on a complex ball containing [0,1]. This proves normalization without dividing by Z or assuming its nonvanishing.

This is the determinant prefactor for finite Gaussian sewing. It does not construct the full corrected field sewing identity, coordinate transport for arbitrary possibly degenerate Gram matrices, countable-mode limits, a complete conformal field theory, string theory or an AdS/CFT realization. Those bridges remain separate mathematical problems.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.annihilate`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_add`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_const`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_pair_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_single`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_square_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_sum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.created_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.gaussian_annihilate`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.insertion`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_comm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_const_right`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_creation_annihilation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.pairing_sum_right`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.vacuumTraceLog`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum.vacuum_trace_log`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FactorialFockQuadraticEstimate](FactorialFockQuadraticEstimate.md)

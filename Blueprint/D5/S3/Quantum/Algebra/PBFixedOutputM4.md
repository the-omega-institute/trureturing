# Full M4 realization and original spectral probes

## Abstract

The full self-adjoint M4 carrier realizes the scalar PB vector model. All four coordinates remain in the vector states. For the original diagonal actor and two-leg star, scalar PB for every positive complex-linear functional and every actor-supported Hermitian probe forces a real diagonal residual on the full four-dimensional output. Its environment entry is unrestricted.

**Definition 1.1 (The original actor).**

$$m4C = \operatorname{diag}\left(1, 2, 3, 0\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first three spectral values are 1, 2 and 3; the fourth, environment value is zero.

**Definition 1.2 (The original two-leg star).**

$$\operatorname{m4T}\left(q1, q2\right) = \operatorname{HermitianStar}\left(q1, q2, 0\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actor-to-environment column is exactly (q1,q2,0), with its conjugate row. No phase rotation is performed.

**Definition 1.3 (The oriented commutator).**

$$\operatorname{m4Kappa}\left(c, iota, x\right) = \operatorname{OrientedHalfCommutator}\left(iota, c, x\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4Kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real-linear row is iota times (cx-xc)/2, with iota fixed as either i or minus i.

**Definition 1.4 (The concrete M4 Jordan product).**

$$m4J = \operatorname{M4JordanProduct}\left(\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is the real self-adjoint submodule of Matrix (Fin 4) (Fin 4) Complex, with literal symmetrized matrix multiplication.

**Definition 1.5 (The concrete M4 vector model).**

$$m4VectorModel = \operatorname{VectorModel}\left(\operatorname{EuclideanSpace}\left(Complex, \operatorname{Fin}\left(4\right)\right), m4J\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4VectorModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operator is literal matrix action on the entire four-dimensional Euclidean space; the environment coordinate remains in the representation.

**Theorem 1.6 (Hermitian full-row reconstruction).**

$$\operatorname{HermitianRowReconstruction}\left(g, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4_full_row_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Agreement on every off-diagonal entry of two Hermitian four-by-four matrices leaves a diagonal residual with real entries.

**Definition 1.7 (A full-space vector functional).**

$$m4VectorFunctional = \operatorname{VectorState}\left(v\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4VectorFunctional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex-linear vector state is evaluated on the whole M4 carrier.

**Definition 1.8 (Real restriction of a complex functional).**

$$m4RealFunctional = \operatorname{RealRestriction}\left(phi\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4RealFunctional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restriction to the self-adjoint real carrier takes the real part.

**Theorem 1.9 (Vector restriction identity).**

$$\operatorname{RestrictionEqualsVectorReading}\left(v, A\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4RealFunctional_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For vector states, the restriction is exactly the existing vectorReading.

**Definition 1.10 (Full complex positive cone).**

$$m4PosSemidef = \operatorname{HermitianQuadraticNonnegative}\left(\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4PosSemidef` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive semidefiniteness is stated as Hermiticity plus nonnegative full-space quadratic forms, avoiding an order on Complex.

**Definition 1.11 (Full matrix positivity predicate).**

$$m4Positive = \operatorname{PositiveFunctionalOnM4}\left(\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4Positive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The predicate requires a real, nonnegative value on every matrix in the complete positive cone.

**Theorem 1.12 (Vector states are positive).**

$$\operatorname{m4Positive}\left(\operatorname{m4VectorFunctional}\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4VectorFunctional_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic-form definition proves positivity of every full-space vector state.

**Definition 1.13 (Original actor support).**

$$m4ActorSupported = \operatorname{FourthRowAndColumnZero}\left(\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4ActorSupported` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actor-supported probes retain the original four-by-four carrier while forcing the fourth row and column to vanish.

**Theorem 1.14 (Positive-functional PB to vector PB).**

$$\operatorname{PositivePBTransfer}\left(hPB\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4_positive_pb_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the original scalar PB to a positive vector state supplies the full-space vector-reading hypothesis used by the Gram argument.

**Theorem 1.15 (Scalar PB reconstructs the complete original output).**

$$\forall q1 \in \mathbb{C},\; \forall q2 \in \mathbb{C},\; \left(q1 \cdot q2 = 0 \Rightarrow False\right) \Rightarrow \left(\forall iota \in \mathbb{C},\; \left(iota = i \lor iota = -i\right) \Rightarrow \left(\forall g \in \operatorname{selfAdjoint}\left(\operatorname{M4}\left(\mathbb{C}\right)\right),\; \left(\forall phi \in \operatorname{ComplexLinearFunctional}\left(\operatorname{M4}\left(\mathbb{C}\right)\right),\; \operatorname{m4Positive}\left(phi\right) \Rightarrow \left(\forall x \in \operatorname{selfAdjoint}\left(\operatorname{M4}\left(\mathbb{C}\right)\right),\; \operatorname{m4ActorSupported}\left(x\right) \Rightarrow \operatorname{scalarPB}\left(m4J, \operatorname{m4Kappa}\left(m4C, iota\right), \operatorname{m4J}\left(m4C\right), \operatorname{m4T}\left(q1, q2\right), \operatorname{m4J}\left(m4C, \operatorname{m4T}\left(q1, q2\right)\right), g, x, \operatorname{m4RealFunctional}\left(phi\right)\right)\right)\right) \Rightarrow \left(\exists s \in \operatorname{Function}\left(\operatorname{Fin}\left(4\right), \mathbb{R}\right),\; g - \operatorname{m4Kappa}\left(m4C, iota, \operatorname{m4T}\left(q1, q2\right)\right) = \operatorname{diagonal}\left(\operatorname{ofReal}\left(s\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4_scalar_pb_diagonal_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take c=diag(1,2,3,0) and t with actor-to-environment column (q1,q2,0), q1 q2 nonzero, and its conjugate row. Fix iota as either i or minus i. The unknown g is any Hermitian M4 matrix. For every positive complex-linear functional phi on the full M4 algebra and every Hermitian probe x with fourth row and column zero, assume scalarPB with kappa(x)=iota(cx-xc)/2, rho(x)=(cx+xc)/2 and k=(ct+tc)/2. The conclusion gives four real diagonal residuals of g-iota(ct-tc)/2, including an unrestricted environment entry. There is no total response map or independent P2 assumption.

For distinct actor indices i,j, construct e from the two matrix units, j0 with coefficients iota and minus iota, and n=2 times the i-th spectral projection. Literal matrix multiplication supplies the spectral pair, its companion axis, and J(n,V)=V, where V=c_i J(n,t)-J(n,J(c,t)). Both probe families T e+alpha n and T j0+alpha n are actor-supported.

For a unit vector xi with xi_i=0, put y=j0 xi and d=norm(y). If d=0 the quadratic reading vanishes. Otherwise eta=y/d is unit, e xi=-iota y and n eta=2 eta. Apply fixed_output_two_axis_identity on the whole M4 representation. Homogeneous scaling gives inner(j0 xi,g xi)=iota inner(j0 xi,V xi) for every xi with xi_i=0, including zero vectors.

Let P_i remove coordinate i, let Y represent j0 and let A represent g-iota V. The quadratic identity makes the quadratic form of P_i Y A P_i vanish on every full-space vector. Mathlib's complex polarization theorem inner_map_self_eq_zero gives P_i Y A P_i=0. Its j-th output coordinate on each complementary basis vector forces the entire i-th row of A to vanish off the diagonal. The entry formula identifies iota V with the corresponding commutator row. Repeat for all three actor indices; Hermiticity supplies the matching environment row, leaving four real diagonal entries. Each quadratic form uses one common j0 and retains the fourth input coordinate.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4ActorSupported`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4C`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4J`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4Kappa`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4PosSemidef`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4Positive`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4RealFunctional`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4RealFunctional_vector`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4T`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4VectorFunctional`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4VectorFunctional_positive`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4VectorModel`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4_full_row_reconstruction`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4_positive_pb_transfer`
- Truth anchor: `D5/S3/Quantum/Algebra/PBFixedOutputM4.m4_scalar_pb_diagonal_residual`
- Dependency: [D5/S3/Quantum/Algebra/PBFixedOutputGram](PBFixedOutputGram.md)

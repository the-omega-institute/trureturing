# Lattice coset compression

## Abstract

LatticeCosetCompression

**Definition 1.1 (ambient).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.ambient`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.ambient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every native LatticeData D, external rank e, integral rectangular B and integral symmetric even-diagonal C, the ambient Gram matrix has blocks G,B,B transpose,C, with old coordinates first. Neither block is required to have positive rank. The native actualVertexAlgebra accepts this ambient without any positivity premise.

**Definition 1.2 (liftCharge).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.liftCharge`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.liftCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ambient charge joins an arbitrary original integral charge n to an arbitrary external integral charge a, in that order.

**Definition 1.3 (oldCharge).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.oldCharge`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.oldCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restriction of an arbitrary ambient charge to the old coordinates.

**Definition 1.4 (externalCharge).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.externalCharge`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.externalCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restriction of an arbitrary ambient charge to the external coordinates.

**Definition 1.5 (polynomialInjection).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.polynomialInjection`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.polynomialInjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rename every original oscillator variable to its old ambient coordinate, preserving its nonnegative oscillator index.

**Definition 1.6 (longitudinal).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.longitudinal`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.longitudinal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational matrix inverseRat(D) times B; no integral inverse is assumed.

**Definition 1.7 (projectionVariable).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projectionVariable`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projectionVariable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Old oscillator variables are fixed. External variable (j,k) is replaced by the sum over old i of the complex cast of (HB)(i,j) times X(i,k).

**Definition 1.8 (polynomialProjection).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.polynomialProjection`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.polynomialProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex algebra homomorphism specified by projectionVariable, on all ambient oscillator polynomials.

**Definition 1.9 (injection).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.injection`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.injection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any external charge a, J_a takes every original finite-charge state single(n,p) to single((n,a),rename_old(p)), extended complex linearly.

**Definition 1.10 (projection).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projection`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any external charge a, P_a selects exactly that external charge, restricts the remaining charge to the old block, and applies polynomialProjection to its complete oscillator polynomial.

**Definition 1.11 (compressed).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.compressed`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.compressed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary external a,b, original state u and integer mode m, Z_ab(u,m) is the complex linear map P_(a+b) composed with the actual ambient mode Y_E(J_a u)[m] composed with J_b. These are the native all-state fields, with their original epsilon and half-diagonal term.

**Definition 1.12 (schur).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.schur`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.schur` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary external integral a,b, the rational scalar a transpose (C minus B transpose H B)b, in the displayed charge order.

**Definition 1.13 (correction).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.correction`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.correction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary external a,b and natural j, the complex scalar (-1)^j times the rational binomial choose(schur(a,b),j).

**Theorem 1.14 (projection_weightedPartial).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projection_weightedPartial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projection_weightedPartial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite original D, arbitrary B,C as above, every old direction i, natural frequency r and every ambient polynomial p, applying the old Gram-weighted positive Heisenberg derivative and then polynomialProjection equals applying polynomialProjection and then the original Gram-weighted derivative. The equation G HB=B is derived using the existing inverseRat API; no ambient positivity is used.

**Theorem 1.15 (projection_current_polynomial).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projection_current_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projection_current_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite original D, every old i, arbitrary ambient charge n, integer mode m and ambient polynomial p, projection of the original ambient current mode equals shiftedCurrentPolynomial on the projected p. The original charge is oldCharge(n), and its integral dual-pairing shift is B times externalCharge(n). This includes negative creation modes, the shifted zero mode and positive annihilation modes.

**Theorem 1.16 (compressed_high_modes).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.compressed_high_modes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.compressed_high_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every external a,b, arbitrary original u,v and integer q, there is a natural N such that Z_ab(u,q+j)v is zero whenever N is at most j. This is actual statewise truncation with no degree restriction on u or v.

**Theorem 1.17 (correction_finite).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.correction_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.correction_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all external a,b,c, arbitrary original u,v,w and integers p,q, the proposed correction summand (-1)^j choose(s(a,b),j) times Z_(a,b+c)(u,p-j)(Z_(b,c)(v,q+j)w) has finite support on natural j. The inner actual field supplies the cutoff.

The field conventions and classical construction are those of Bakalov-Kac, math/0402315v1, section 4.1. The imported native normal products and residue constructions retain their Carnahan Apache-2.0 attribution. These definitions and truncation bounds supply the prerequisites and exact finite summand support used by LatticeCosetOperatorCorrection. Phase descent, analytic CFT and string-theory or AdS/CFT realization are outside these statements.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.ambient`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.compressed`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.compressed_high_modes`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.correction`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.correction_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.externalCharge`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.injection`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.liftCharge`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.longitudinal`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.oldCharge`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.polynomialInjection`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.polynomialProjection`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projection`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projectionVariable`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projection_current_polynomial`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.projection_weightedPartial`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetCompression.schur`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta](../Characters/LatticeDiscriminantTheta.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule](LatticeDualCosetModule.md)

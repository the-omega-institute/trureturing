# Doubled Gram sectors and forward modular transformations

## Abstract

Source-coupled theta laws in the original mod-two charge sectors

**Definition 1.1 (Doubled Gram form).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.doubled`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.doubled` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep the integral coordinates of D and double its Gram matrix G.

**Definition 1.2 (Additive equivalence of charge sectors).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.sectorEquiv`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.sectorEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If det G is a unit in ℤ, the mod-two reduction of q corresponds to [Gq] in the Gram cokernel ℤʳ/(2G)ℤʳ. Equality of these classes is equivalent to equality of the mod-two reductions. The dual shift at Gq is q/2.

**Definition 1.3 (Theta series at an original charge sector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a mod-two charge a, Θₐ(τ,z) is the shifted theta series at its doubled-Gram class, with complex period τ and complex vector source z.

**Theorem 1.4 (Forward S with a complex source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_S`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_S` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume det G is a unit in ℤ, G is positive definite over ℝ, the rank is 24 and Im τ > 0. With Q₂(z) = z · (2Gℂ)z, the theta series at (−1/τ,z/τ) equals (−iτ)¹² exp(πi Q₂(z)/τ) times 2⁻¹² Σᵦ fourierSign(a,b) Θᵦ(τ,z). The doubled-Gram pairing at Gq and Gp is bilinear(D,q,p)/2, which matches the original cocycle sign. Apply `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantShiftedTheta.shiftedTheta_S` and invert its finite Fourier transform using `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.finite_weil_relations`.

**Theorem 1.5 (Theta series over the integral charge fiber).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_eq_charge_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_eq_charge_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If det G is a unit in ℤ, for every complex τ and z, Θₐ(τ,z) is the topological sum over integral q reducing to a of exp(πiτ bilinear(D,q,q)/2 + 2πi (Gℂq) · z). Here Gℂ denotes the complex cast of G and the dot product is complex bilinear.

**Theorem 1.6 (Unit translation at fixed source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_T`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_T` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If det G is a unit in ℤ and G is positive definite over ℝ, then Θₐ(τ+1,z) = quadraticSign(a) Θₐ(τ,z) for every complex τ and z. The doubled-Gram quadratic class at Gq is represented by bilinear(D,q,q)/4.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantShiftedTheta.shiftedTheta_S`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeDiscriminantWeil.finite_weil_relations`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_S`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_T`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.chargeTheta_eq_charge_sum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.doubled`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta.sectorEquiv`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeDiscriminantShiftedTheta](../../Characters/LatticeDiscriminantShiftedTheta.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy](../../LatticeHalfFockChargedMonodromy.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset](../OriginalFourMChargeCoset.md)

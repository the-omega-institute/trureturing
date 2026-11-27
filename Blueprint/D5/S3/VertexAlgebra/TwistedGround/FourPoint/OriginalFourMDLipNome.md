# Signed continuation at the D boundary

## Abstract

The original lattice nome on the D lip

**Definition 1.1 (The continued period ratio).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dTau`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dTau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let τ be the original slit-period ratio. For a Boolean upperA and complex t, set dTau(upperA,t) = −(τ(1−1/t) + s)⁻¹. When upperA is true, s = 1 and the selected D lip has Im t < 0. When upperA is false, s = −1 and the selected D lip has Im t > 0.

**Definition 1.2 (The continued lattice nome).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either Boolean upperA and every complex t, dNome(upperA,t) = exp(iπ dTau(upperA,t)).

**Theorem 1.3 (Ratio agreement on the open lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dTau_eq_tau`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dTau_eq_tau` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Boolean upperA and every complex t on the selected open D lip, dTau(upperA,t) = τ(t).

**Theorem 1.4 (Nome agreement on the open lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_eq_exp`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_eq_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Boolean upperA and every complex t on the selected open D lip, dNome(upperA,t) equals the original lattice nome exp(iπ τ(t)).

**Theorem 1.5 (Analyticity at the D boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_analyticAt`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_analyticAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Boolean upperA and every real t > 1, the function u ↦ dNome(upperA,u) is complex analytic at t viewed in ℂ.

**Theorem 1.6 (Strict norm bound at the D boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_norm_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_norm_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Boolean upperA and every real t > 1, ‖dNome(upperA,t)‖ < 1 at the complex boundary point t.

**Theorem 1.7 (Strict norm bound in a complex neighborhood).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_subunit_near`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_subunit_near` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either Boolean upperA and every real t > 1, ‖dNome(upperA,u)‖ < 1 for all u in some complex neighborhood of t.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_analyticAt`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_eq_exp`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_norm_lt_one`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dNome_subunit_near`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dTau`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome.dTau_eq_tau`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource](OriginalFourMPeriodSource.md)

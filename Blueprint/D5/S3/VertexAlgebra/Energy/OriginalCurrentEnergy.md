# The original Hermitian norm and current estimates

## Abstract

Full-frame positivity and uniform original-current estimates consumed by the original lattice energy bounds.

**Definition 1.1 (The original Hermitian norm).**

Lean statement: `D5/S3/VertexAlgebra/Energy/OriginalCurrentEnergy.normD`

*Formalization.* `D5/S3/VertexAlgebra/Energy/OriginalCurrentEnergy.normD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every original D and v:Carrier(D), normD(v)=sqrt(Re(Hm(v,v))), where Hm is OriginalMatterHermitian.Hm. The definition has no positivity premise. The proofs derive its definiteness and norm laws from positive definiteness of the original real Gram matrix, using a full real orthonormal frame and its inverse substitution.

The full real orthonormal frame uses the actual positive-definite real Gram matrix and its inverse substitution. Surjectivity transfers the existing transverse factorial pairing to every original finite charge/oscillator state, proving positivity and the norm laws, including rank zero. The public normD name is unchanged; its defining source is now this support module.

For integer frequency r+1 the exact oscillator weight is product e(i,r)!*(r+1)^e(i,r). The frequency derivative sum equals the weighted occupation number. Finite vector-valued Cauchy-Schwarz controls arbitrary colour directions, retaining cross-colour interference; adjointness and the exact commutator control creation. Full inverse-frame substitution translates these inequalities back to each original current. Orthogonality sums all charge sectors without a support-cardinality factor. Gram Cauchy-Schwarz controls the charge zero mode.

The resulting private original_current_energy_le bounds each signed original neutral current between finite energy grades by sqrt(3*G(i,i))*(M+1)*normD(v). It and the norm laws are consumed by OriginalNeutralEnergy, and positivity is also consumed by the charged normal-product argument. Existing full-frame, factorial, transpose and Mathlib suppliers retain their attributions. These moved proof components add no standalone mathematical result, no new public theorem and no new registration target; the existing charged/neutral Reg evidence remains with OriginalChargedEnergy.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Energy/OriginalCurrentEnergy.normD`
- Dependency: [D5/S3/VertexAlgebra/Energy/LatticeCoefficientEnergy](LatticeCoefficientEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeLightConeCoordinates](../Lattice/LatticeLightConeCoordinates.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](../LatticeActualConformalState.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus](../LatticeActualStateFieldCalculus.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/ChargedRawTranspose](../SourceBPZ/ChargedRawTranspose.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/TransverseHermitian](../SourceBPZ/TransverseHermitian.md)

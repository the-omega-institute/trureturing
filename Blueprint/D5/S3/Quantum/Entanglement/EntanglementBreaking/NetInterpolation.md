# Interpolation from finite nets

## Abstract

Bilinear and quadratic interpolation of finite net estimates.

**Theorem 1.1 (Bilinear net for bounded Schmidt rank).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.exists_schmidt_bilinear_net`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.exists_schmidt_bilinear_net` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Approximation of each factor yields two error terms controlled by the restricted bilinear bound. The net radius allows these errors to be absorbed into that bound.

**Theorem 1.2 (Quadratic net controls the Hermitian operator norm).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.exists_full_sphere_quadratic_net`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.exists_full_sphere_quadratic_net` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Approximate a unit vector on both sides of its quadratic form. Hermiticity relates the supremum of the absolute quadratic form to the operator norm.

**Definition 1.3 (Coeff vector).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.coeffVector`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.coeffVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Turn a coefficient matrix into the Euclidean vector with the same entries, indexed by the product of the row and column types.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.coeffVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.exists_full_sphere_quadratic_net`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/NetInterpolation.exists_schmidt_bilinear_net`
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet](RankNet.md)

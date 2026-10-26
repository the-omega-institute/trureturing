# Coupled balanced Jacobi cancellation

## Abstract

Coupled balanced Jacobi cancellation

**Definition 1.1 (The actual balanced tree).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBalancedBorcherds.balanced`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorBalancedBorcherds.balanced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual coefficient is canonical(α+β,γ+δ)(canonical(α,β)u(-s-1)v)(-x-1)(canonical(γ,δ)t(-z-1)w). The coefficient order is [s,x,z].

**Definition 1.2 (Literal original clearing).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBalancedBorcherds.clearedBalanced`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeSectorBalancedBorcherds.clearedBalanced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite j,l sum has coefficients (-1)^(j+l) binom(k,j) binom(k,l), and applies clearIterate k (a0+k-j) (a1+k-l) to the balanced coefficient at z-a2-j-l. It is exactly the expansion of (s+x)^a0 x^a1 z^a2 s^k (s+x-z)^k (x-z)^k. The full integer Borcherds identity is used. For fixed l and Jacobi offset i, the j-sum of its second term is the original u/t locality sum. Moving u past t places u directly on w at mode a0+k-j+i, where the original a0 cutoff kills it. No cutoff of u on t_z w is assumed or chosen. All finite-sum exchanges retain their actual finite-support proofs. Suppliers retain Bakalov--Kac, Matsuo--Nagatomo and Carnahan attribution.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBalancedBorcherds.balanced`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeSectorBalancedBorcherds.clearedBalanced`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision](../FormalSeries/SupportedBalancedCollision.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorChannelTransport](LatticeSectorChannelTransport.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldCommonSeries](LatticeSectorThreeFieldCommonSeries.md)

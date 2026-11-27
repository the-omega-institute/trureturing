# Primary coefficient selection for the original Ising axis

## Abstract

Primary coefficient selection for the original Ising axis

**Theorem 1.1 (Allowed primary weights).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingPrimaryCoupling.originalI_ising_primary_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingPrimaryCoupling.originalI_ising_primary_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D be a positive definite rank-24 lattice with unit Gram determinant. Use an axis from a charge of norm four and a sign s with s² = 1. Take u and v in the negative twisted carrier with axis weights h₁ and h₂, both killed by every positive axis mode. Let a complex-linear detector ℓ on the fixed carrier satisfy ℓL(0) = h₃ℓ and ℓL(k) = 0 for every negative integer k. All three weights belong to {0, 1/2, 1/16}.

For any integer n with ℓ(Iₙ(u,v)) ≠ 0, where I is the original two-twisted coefficient, an input of weight zero forces h₃ to equal the other input weight. Two inputs of weight 1/2 require h₃ = 0. Mixed inputs of weights 1/2 and 1/16 require h₃ = 1/16. Two inputs of weight 1/16 allow h₃ in {0, 1/2}. These are necessary conditions for a nonzero detected coefficient.

Write δ = h₃ − h₁ − h₂ and c = ℓ(Iₙ(u,v)). The mixed Jacobi identity gives the detected first descendant at mode n+1 as δc and the detected second descendant L(−2)u at mode n+2 as (h₁ + 2h₂ − h₃)c. In the second identity the fixed-carrier sum is finite by truncation, and the detector kills each summand. The Virasoro commutator gives the iterated first descendant at mode n+2 as (δ−1)δc. The odd null laws and c ≠ 0 reduce the table to arithmetic in the three candidate weights.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingPrimaryCoupling.originalI_ising_primary_selection`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateFieldCalculus](../../LatticeActualStateFieldCalculus.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight](FixedSourceIsingHighestWeight.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSourceModeTransport](OriginalSourceModeTransport.md)

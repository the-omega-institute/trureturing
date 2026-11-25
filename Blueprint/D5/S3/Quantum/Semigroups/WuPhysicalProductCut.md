# Two-mode CAR product cuts

## Abstract

Physical rank-two cuts and exact Hilbert–Schmidt transport for Wu’s two signed CAR modes.

For the two-mode cubic setting of Wu v1, equation (3.54), use occupation order 00, 01, 10, 11 and ordinary matrix trace. The degree-one frame consists of I⊗X, I⊗Y, X⊗Z, Y⊗Z. The occupation imbalance F is diag(1, 0, 0, −1). For a unit frame direction G, its paired observable is Z(G) = F − GFG and the cut is Q = (I + uG + ρZ(G))/2.

**Theorem 1.1 (Rank and occupation imbalance).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPhysicalProductCut.carProductCut_projection`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPhysicalProductCut.carProductCut_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For unit real direction coefficients and u² + ρ² = 1, Q is Hermitian and idempotent, has ordinary trace 2, and has Re Tr(FQ) = ρ. The construction uses two anticommuting Hermitian involutions G and Z(G).

**Theorem 1.2 (Product form under the signed mode rotation).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPhysicalProductCut.carProductCut_modeRotation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPhysicalProductCut.carProductCut_modeRotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The unitary U fixes the empty and doubly occupied states in the construction and commutes with F. It conjugates I⊗q to Q, where q = (I + uX + ρZ)/2. For the literal lowering operators J₁ = E₀₁ − E₂₃ and J₂ = E₀₂ + E₁₃ in occupation order, conjugation sends J₁ to zJ₁ + wJ₂ and J₂ to −w̄J₁ + z̄J₂, where z = a − ib and w = c − id.

**Theorem 1.3 (Exact transport to a CAR cut).**

Lean statement: `D5/S3/Quantum/Semigroups/WuPhysicalProductCut.carProductCut_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuPhysicalProductCut.carProductCut_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Let k be the Euclidean norm of the four real Pauli coefficients Re Tr(HW)/4, let R = Re Tr(FP), and let θ = √(k² + R²). There is a unit direction and a unit real pair (u, ρ) with θ ≤ 1, θu = k, and θρ = R. The resulting cut is Hermitian and idempotent with trace 2, imbalance ρ, and ordinary squared Hilbert–Schmidt distance 2(1 − θ) from P. When k vanishes, the traceless parts of the parity blocks have matching squared norms, so the construction covers all complex rank-two projections.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuPhysicalProductCut.carProductCut_modeRotation`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPhysicalProductCut.carProductCut_projection`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuPhysicalProductCut.carProductCut_transport`
- Dependency: [D5/S3/Quantum/Semigroups/WuRankOneEndpointClifford](WuRankOneEndpointClifford.md)

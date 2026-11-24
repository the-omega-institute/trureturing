# Rotated BKM energy of a qubit Petz pencil

## Abstract

The physical partial-trace Petz pencil has an exact rotated BKM energy with three logarithmic means.

**Theorem 1.1 (Physical pencil, spectral identity and weighted bound).**

Lean statement: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzRotatedBKM.physical_pencil_rotated_bkm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzRotatedBKM.physical_pencil_rotated_bkm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the environment be any finite index set with strictly positive populations g summing to one. Take retained populations p and q strictly between zero and one and a complex unitary V on the qubit. Write Q for diag(q, 1−q), γ for diag(g), Σ for Q tensor γ, τ for V diag(p, 1−p) V*, and D for τ tensor γ.

For an arbitrary complex environment matrix H, a link from j to i is active when H(i,j) is nonzero. Its frequency r(i,j) is q g(j) divided by (1−q) g(i). Suppose every active frequency is at least rmin, where rmin is positive and q divided by (1−q) rmin is less than one. For each active link, g(i)/g(j) is at most q divided by (1−q) rmin. The strict cutoff rules out loops and pairs of reciprocal links.

Set U = E₁₀ tensor H plus its adjoint. The entrywise tangent X is Σ^(1/2) U Σ^(1/2), and σ = Σ + s X for real s. The physical partial trace of σ is Q. The partial-trace Petz formula at σ applied to τ equals S (R D R) S with S = σ^(1/2) and R = Σ^(−1/2). At positive definite σ this is the ordinary faithful-reference Petz recovery.

Write Λ(x,y) for the integral of x^t y^(1−t) from zero to one. The resolvent logarithmic derivative L of Σ in direction X is E₁₀ tensor C plus its adjoint, where C(i,j) = sqrt(r(i,j)) H(i,j) / Λ(r(i,j),1). Set w = 1−|V(0,0)|² and P = p(1−w)+(1−p)w. The first physical diagonal entry of τ is P.

Half the real trace of L Ω_D(L) is the sum over ordered pairs (i,j) of |C(i,j)|² times the sum of three terms. They are (1−w)² Λ((1−p)g(i), p g(j)), w² Λ(p g(i), (1−p)g(j)), and w(1−w) Λ(g(i), g(j)). The two retained diagonal contributions combine by homogeneity of Λ. The adjoint contributes the same sum, since the two environmental orientations have disjoint support and Λ is symmetric.

Replacing the three logarithmic means by their arithmetic upper bounds gives the sum over (i,j) of |C(i,j)|² ((1−P)g(i) + P g(j)) / 2.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/NoncommutingQubit/PetzRotatedBKM.physical_pencil_rotated_bkm`
- Dependency: [D5/S3/Divergence/MeanKernels/LogarithmicMeanSandwich](../../../Divergence/MeanKernels/LogarithmicMeanSandwich.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiRareFlagBKM](../../Divergence/UmegakiRareFlagBKM.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMFlagRefinementPetz](../BKMFlagRefinementPetz.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMSpectralVariance](../BKMSpectralVariance.md)

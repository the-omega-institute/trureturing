# One Determinant

## Abstract

One Determinant

Positive-type functions avoid singular minors; Hilbert-Schmidt variance inequality giving spread. Few translates nearly span; height bound for a ratio of Gram determinants.

**Theorem 1.1 (one_determinant).**

Lean statement: `D5/S3/Zeros/GRH/New/Heights/OneDeterminant.one_determinant`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Heights/OneDeterminant.one_determinant` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

One determinant. Let x be a basis of W, u o injective, all conjugates of the Gram determinant of u o ∘ x of modulus ≤ exp α, γ nonzero with |γ|⁻² of height ≤ g, all finite sums of e at most δ. If for all ι at l and j : ℂ → ℂ_l the pairing of Λ ι (j∘conj) with Λ ι j is j-integral and a complex matrix m with |j(det m)| ≥ exp(−e l)·|j(γ ι)|^k recombines u (θ ι) ∘ x into Λ ι j, then the squared-volume ratios of u (θ ι) to u o have height ≤ α + 2δ + kg.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Heights/OneDeterminant.one_determinant`
- Dependency: [D5/S3/Zeros/GRH/New/Heights/Heights](Heights.md)

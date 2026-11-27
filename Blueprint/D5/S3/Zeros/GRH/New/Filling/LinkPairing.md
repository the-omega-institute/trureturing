# Link Pairing

## Abstract

Link Pairing

Bordered determinant bounds the discriminant of the lattice of lifts of a link. Discriminant gain for congruent terms with differing links, via lattices of lifts.

**Theorem 1.1 (pairInvariant_mul_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/LinkPairing.pairInvariant_mul_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/LinkPairing.pairInvariant_mul_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For γ, γ' of level j over one agreeing s with Filling.FixesNormAtLeast s x, some i has |κ| ≤ dim T° + i + (j−ϱ)₊ (T° = commonLink γ γ'), is 0 only for equal links, and P(γ,γ')P(γ',γ)x'² ≤ (2/g)^(2if)·G(γ)G(γ') (P = Filling.pairInvariant, G = Filling.classGauge j c c'); x' = x if j > ϱ and i = 0, else 1.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/LinkPairing.pairInvariant_mul_le`
- Dependency: [D5/S3/Zeros/GRH/New/Filling/BoxPartition](BoxPartition.md)

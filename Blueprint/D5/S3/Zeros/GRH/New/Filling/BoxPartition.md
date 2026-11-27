# Box Partition

## Abstract

Box Partition

Positive form on links, lifts to the lattice, dimension and isotropy of links. Primes where agreeing frames meet divide a determinant; integral Eichler lifts. Integral Eichler transformations give elements of the level-g unipotent group of a class. Covering lemmas for weighted sums; counting bounded integral vectors; index of a scaled lattice. Definitions of indices, discriminants, gauges and class representatives for the crude bounds. Boxed cutoffs for the arithmetic unipotent group and packing count of boxed frames.

**Theorem 1.1 (tsum_classCutoff_box_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Filling/BoxPartition.tsum_classCutoff_box_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Filling/BoxPartition.tsum_classCutoff_box_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Frame count: let w_p ≤ β_{k_p}(δ_p⁻¹y')·x, with p ↦ (k_p, δ_p) injective. If, where w_p ≠ 0, γ_p ∈ δ_p𝖴_{k_p}(g) lies over (c,s,k_p), γ_p⁻¹y ∈ Filling.boxedPoints, and the frames y⁻¹γ_pf differ in a real subspace V, then ∑w_p ≤ b^(6(ϱ+1)² dim V)·x.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Filling/BoxPartition.tsum_classCutoff_box_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/PartnerAlgebra](../../Lib/General/LinearAlgebra/PartnerAlgebra.md)
- Dependency: [D5/S3/Zeros/GRH/New/Filling/NearTerms](NearTerms.md)

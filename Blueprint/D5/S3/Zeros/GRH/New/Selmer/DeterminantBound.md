# Determinant Bound

## Abstract

Determinant Bound

Bloch–Kato finite condition at places above ℓ as relations on global cocycles. Conditions on Hodge-Tate jumps of a row; explicit crystalline loss per prime. Dictionary between complex embeddings, places above l and cosets of local Galois groups. Operators clearing denominators at each eigenvector combine to bound the Gram determinant.

**Theorem 1.1 (norm_gram_det_le_of_operators).**

Lean statement: `D5/S3/Zeros/GRH/New/Selmer/DeterminantBound.norm_gram_det_le_of_operators`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Selmer/DeterminantBound.norm_gram_det_le_of_operators` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let A span Z, of finite dimension, x_b ∈ Z. Suppose each nonzero p ∈ A has a map G, a multiple of j on each v ∈ A, whose scalars ι⁻¹(l) at p have ‖lm‖ ≥ e^{−γ}, and ‖m·ιη_a(w)‖ ≤ 1 if w ∈ Z, jw = Gx_b. Then ‖ι det η_a(x_b)‖ ≤ e^{γ dim Z}.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Selmer/DeterminantBound.norm_gram_det_le_of_operators`
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/WachKisin/HodgeFrame](../../Lib/PadicHodge/WachKisin/HodgeFrame.md)
- Dependency: [D5/S3/Zeros/GRH/New/Data/Weights](../Data/Weights.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/BlocksAndCocycles](BlocksAndCocycles.md)

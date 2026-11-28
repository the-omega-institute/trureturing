# Depth Pairs

## Abstract

Depth Pairs

Choice of admissible pairs and numerical bound against the predicted valuation F(p). Pairs construction: Frobenius couplings force a large coefficient on six copies.

**Theorem 1.1 (exists_hasLargeSplit_of_pairs).**

Lean statement: `D5/S3/Zeros/GRH/New/Curve/DepthPairs.exists_hasLargeSplit_of_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Curve/DepthPairs.exists_hasLargeSplit_of_pairs` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let (p/d) ≠ 1, Θ in Parameters.thetaProducts (δ = r = 1, one copy), Θ(0) = 1, Θ carried by one copy and Θ⁻¹ by five (IsCarriedBy), (i, y) admissible for n (IsFrobPacking). Then some b, τ ≤ n with |b| = ∑y_σ(p^{i_σ} + 1), |τ| = ∑y_σ satisfy HasLargeSplit N 6 b (p^{(1 − 1/(p−1))|τ| + ρ_p|b|}/|τ!|_p).

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Curve/DepthPairs.exists_hasLargeSplit_of_pairs`
- Dependency: [D5/S3/Zeros/GRH/New/Curve/LiveSum](LiveSum.md)
- Dependency: [D5/S3/Zeros/GRH/New/Data/Weights](../Data/Weights.md)

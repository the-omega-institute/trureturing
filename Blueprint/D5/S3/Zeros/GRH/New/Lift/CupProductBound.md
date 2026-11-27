# Cup Product Bound

## Abstract

Cup Product Bound

a cup product of crystalline cocycles is a coboundary if they have lifts to W(C^♭)-coefficients whose Galois and Frobenius differences pair into W(𝔪^♭).

**Theorem 1.1 (of_isSafe).**

Lean statement: `D5/S3/Zeros/GRH/New/Lift/CupProductBound.of_isSafe`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Lift/CupProductBound.of_isSafe` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let e₁ + e₂ + e₃ ≤ e, let x, w lie over p^{e₁}c and x' over p^{e₂}c'. If ((g−1)x, g(h−1)x'), (w−x, (g−1)x'), ((g−1)w, g(φ−1)x'), (φx−w, (g−1)φx') satisfy Lift.Pairing.IsSafe e₃ for all g, h in Γ', then Lift.Pairing.ScaledCupBounds holds for e, c, c'.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Lift/CupProductBound.of_isSafe`
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/BlochKato/BlochKato](../../Lib/PadicHodge/BlochKato/BlochKato.md)

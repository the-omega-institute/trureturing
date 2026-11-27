# Hecke Transfer

## Abstract

Hecke Transfer

Eichler commutation relation of Hecke polynomials through theta lifts at split places.

**Theorem 1.1 (isSphericalWith_formLift).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Weil/Unramified/HeckeTransfer.isSphericalWith_formLift`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Weil/Unramified/HeckeTransfer.isSphericalWith_formLift` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let w be split, ranks n of S, n + k of T, a, b unramified and f the vacuum at w, f an arrow e → e' (IsArrow). If y is spherical at w with Hecke eigenvalue p(X), so is its lift, with ∏_{l<k}(1 − q^{l+n/2}χ_S(w)X)·p(q^{k/2}χ_Sχ_T⁻¹(w)X).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Weil/Unramified/HeckeTransfer.isSphericalWith_formLift`
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/DualPair/PairSumNegation](../DualPair/PairSumNegation.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Lift/Arrow](../Lift/Arrow.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Unramified/UniformiserScalar](UniformiserScalar.md)

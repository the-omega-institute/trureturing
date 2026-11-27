# Sharp Data

## Abstract

Sharp Data

Doubling: inner product of theta lifts as integral of matrix coefficients; dual datum. Reversing a pair: kernel equals reversed kernel with finite Fourier transformed datum. Lifts and descents between discrete series types for families of characters; other polynomials scale. Rank-one unramified doubling sum as Euler factor; sharpness of level data.

**Theorem 1.1 (exists_hasSum_vacuumCoeff_at_place).**

Lean statement: `D5/S3/Zeros/GRH/Lib/SiegelWeil/RallisInner/SharpData.exists_hasSum_vacuumCoeff_at_place`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/SiegelWeil/RallisInner/SharpData.exists_hasSum_vacuumCoeff_at_place` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let ν have trivial tame part at w, w̄, and k > 1. Over some representatives, supported at w, w̄, of U(1)(𝔸_f) modulo elements integral at w, vacuumCoeff(2k, νυ^k) sums to ∏_{u∈{w,w̄}} (1 − ε_u q_u^{−k})/(1 − ν̃(ϖ_u)⁻¹q_u^{−k}), ε = realZetaCoeff, ν̃ = AutChar.baseChange ν.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/SiegelWeil/RallisInner/SharpData.exists_hasSum_vacuumCoeff_at_place`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Groups/IndexOfProduct](../../General/Groups/IndexOfProduct.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelWeilFormula](../Formula/SiegelWeilFormula.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/DualPair/Flip](../../Weil/DualPair/Flip.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Lift/Staircase](../../Weil/Lift/Staircase.md)

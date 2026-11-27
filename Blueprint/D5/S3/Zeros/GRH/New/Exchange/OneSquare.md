# One Square

## Abstract

One Square

Up-then-down and down-then-up theta lifts agree on partner data up to L-values.

**Theorem 1.1 (one_square).**

Lean statement: `D5/S3/Zeros/GRH/New/Exchange/OneSquare.one_square`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Exchange/OneSquare.one_square` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

One square. Let rk A = rk A′ + 2e, q = q(U₁) + q(U₂) = q(A) + q(A′) negative signs, 2q + 2 ≤ n = rk U₁ + rk U₂ ≤ 2μ + 2q, ν tame of weight μ, and the four products of characters equal ν⁻¹υ^⌊n/2⌋ (rankTwist). Send f from U₁ to U₂ along edges, through A (lift, descent) or A′ (descent, lift), with point data at the blocks of x or y. For every functional l the resulting functions of x and y satisfy SquareLaw with constant κ/c (κ may be 0), c ≠ 0, |c|² = C·lValueProd, with C, κ uniform in the family.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Exchange/OneSquare.one_square`
- Dependency: [D5/S3/Zeros/GRH/Lib/SiegelWeil/RallisInner/SharpData](../../Lib/SiegelWeil/RallisInner/SharpData.md)
- Dependency: [D5/S3/Zeros/GRH/New/Exchange/ExchangeTheorem](ExchangeTheorem.md)

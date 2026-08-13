# Golden Deficit Coin Identity

## Abstract

Twice the square of the real golden ratio exceeds its cube by exactly one.

**Theorem 1.1 (The quadratic-cubic deficit is one).**

$$2 \cdot \varphi^{2} - \varphi^{3} = 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/GoldenDeficitCoin.golden_deficit_coin_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The library quadratic identity phi squared equals phi plus one first reduces the cube to phi times phi plus one. A second use of the same identity leaves the exact deficit one.

This is an honest partial closure of only the algebraic identity in the source proposition. The critical-line pullback, structural zero-line interpretation, derivative and slope formula, and all numerical window certificates remain unresolved, so the source atom remains partial and open.

## References

- Truth anchor: `D5/S1/Deficit/GoldenDeficitCoin.golden_deficit_coin_identity`

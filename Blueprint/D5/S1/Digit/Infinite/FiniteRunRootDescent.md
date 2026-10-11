# Finite high-run root descent

## Abstract

Finite high-run roots approach the complete cap root.

**Theorem 1.1 (Strict descent of finite high-run roots).**

Lean statement: `D5/S1/Digit/Infinite/FiniteRunRootDescent.root_rate_chain`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/FiniteRunRootDescent.root_rate_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer k at least two, the finite cap function has a unique root z in the interval (0,1). For every nonnegative index n, with maximum high-run length L = n + 1, the truncated cap function has a unique root zeta(n) in (0,1), and z is strictly below zeta(n). The roots form a strictly decreasing sequence converging to z. Applying the continuous logarithmic rate map gamma(x) = -log(x)/log(2) makes the rates strictly increasing and convergent to the rate of z.

**Definition 1.2 (The root-rate property).**

Lean statement: `D5/S1/Digit/Infinite/FiniteRunRootDescent.root_rate_property`

*Formalization.* `D5/S1/Digit/Infinite/FiniteRunRootDescent.root_rate_property` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root-rate property records the interval membership, root equations, uniqueness of the complete and truncated roots, strict ordering, convergence of the roots, and the corresponding monotonicity and convergence of their logarithmic rates.

## References

- Truth anchor: `D5/S1/Digit/Infinite/FiniteRunRootDescent.root_rate_chain`
- Truth anchor: `D5/S1/Digit/Infinite/FiniteRunRootDescent.root_rate_property`
- Dependency: [D5/S1/Digit/Infinite/ResetCodebookModel](ResetCodebookModel.md)

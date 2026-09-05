# Minimal Positive Repair

## Abstract

The sharp positive repair of the Fibonacci eigenform, with the corrected uniqueness scope.

**Theorem 1.1 (Sharp norm bound, attainment, and spectral minimality).**

$$\begin{aligned}\operatorname{PosSemidef}\left(R\right) \land \operatorname{PosSemidef}\left(F + R\right) \Rightarrow \lvert R \rvert_{op} \ge \varphi^{-1},\\Rmin = \varphi^{-1} \cdot P_{-},\\F + Rmin = \varphi \cdot P_{+},\\\exists Ralt, Ralt \neq Rmin \land \lvert Ralt \rvert_{op} = \varphi^{-1}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/MinimalPositiveRepair.minimal_positive_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Fibonacci form is represented in its expanding and contracting eigenbasis. Positivity on the contracting coordinate forces every feasible repair to have operator norm at least phi inverse.

The negative-part repair attains the bound, leaves phi times the expanding projection, is positive semidefinite, and has rank one. The proof uses Mathlib's L2 matrix operator norm rather than an entrywise norm.

The source's unrestricted uniqueness assertion is false: phi inverse times the identity is a distinct feasible repair with the same norm. The Lean theorem records this counterexample and proves uniqueness only for the coefficientwise least repair diagonal in the Fibonacci eigenbasis.

## References

- Truth anchor: `D5/S1/Eigenstructure/MinimalPositiveRepair.minimal_positive_repair`
- Dependency: [D5/S1/Scale/FibonacciEigen](../Scale/FibonacciEigen.md)

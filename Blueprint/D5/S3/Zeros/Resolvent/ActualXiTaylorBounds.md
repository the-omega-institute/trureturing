# Normal convergence and exact geometric Taylor remainder

## Abstract

Normal convergence and exact geometric Taylor remainder.

**Theorem 1.1 (Normal convergence and exact geometric Taylor remainder).**

Lean statement: `D5/S3/Zeros/Resolvent/ActualXiTaylorBounds.actual_xi_taylor_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Resolvent/ActualXiTaylorBounds.actual_xi_taylor_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep the same actual xi function, nodes, weights, moments, total absolute mass W, and node-norm supremum Lambda. For every nonnegative r less than one quarter, the folded resolvent and its odd Taylor series both have summable uniform majorants on the closed disk of radius r.

The xi function is bounded there by W r divided by (1 minus Lambda r squared). After retaining the odd moment terms through index J, its remainder is at most W r times (Lambda r squared) to power J+1, divided by (1 minus Lambda r squared). The finite sum has exactly J+1 odd terms, and the complete infinite tail is retained in the proof.

The bounds follow from the complex denominator reverse triangle inequality, moment estimates, and a genuinely summable geometric tail. No tail truncation is substituted for the original function, and neither positivity nor RH is used.

## References

- Truth anchor: `D5/S3/Zeros/Resolvent/ActualXiTaylorBounds.actual_xi_taylor_remainder`
- Dependency: [D5/S3/Zeros/Resolvent/ActualXiTaylorDictionary](ActualXiTaylorDictionary.md)

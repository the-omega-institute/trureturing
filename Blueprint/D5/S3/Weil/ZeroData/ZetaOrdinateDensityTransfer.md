# Ordinate transfer from exponential zero density

## Abstract

An exponential right-tail density bound controls the ordinate transfer.

**Theorem 1.1 (Quadratic transfer from the right-tail count).**

Lean statement: `D5/S3/Weil/ZeroData/ZetaOrdinateDensityTransfer.actual_reflection_bound_of_exponential_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ZetaOrdinateDensityTransfer.actual_reflection_bound_of_exponential_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real cutoff T, take the nontrivial zeta zeros with 0 < Im ρ ≤ T, weighted by their analytic multiplicity. Suppose the count with Re ρ ≥ 1/2 + t is bounded by A exp(−rt) for every t > 0, with r > 0. For every real v with |v| ≤ r/4, the norm of the difference between the weighted sums of exp(v(ρ − 1/2)) and exp(iv Im ρ) is at most 64 A (v/r)².

Same-height reflection sends the left tail bijectively to the right tail and preserves multiplicity. Integrating the resulting tail estimate against the derivative of exp(rt/2) bounds the weighted sum of exp(r |Re ρ − 1/2|/2) − 1 by 2 A. The quadratic exponential remainder is dominated by this weight, and the finite reflection bound completes the estimate.

A uniform right-strip density theorem supplies the premise at growing heights.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ZetaOrdinateDensityTransfer.actual_reflection_bound_of_exponential_tail`
- Dependency: [D5/S3/Weil/ZeroData/ZetaOrdinateReflectionTransfer](ZetaOrdinateReflectionTransfer.md)

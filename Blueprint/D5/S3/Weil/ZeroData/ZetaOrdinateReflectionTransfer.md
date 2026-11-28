# From complex zero sums to ordinate sums

## Abstract

Same-height reflection cancels the first-order displacement from the critical line.

**Theorem 1.1 (Quadratic reflection error).**

Lean statement: `D5/S3/Weil/ZeroData/ZetaOrdinateReflectionTransfer.actual_reflection_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ZetaOrdinateReflectionTransfer.actual_reflection_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take every nontrivial zero with 0 < γ ≤ T, with its analytic multiplicity. At any real frequency v, the norm of the difference between the sums of exp(v(ρ − 1/2)) and exp(ivγ) is bounded by the multiplicity-weighted sum of d² exp(d), where d = |v(Re ρ − 1/2)|.

The reflection ρ ↦ 1 − conjugate(ρ) preserves height and multiplicity and reverses the displacement from the critical line. Averaging the original and reflected sums cancels the linear Taylor term. The exponential Taylor remainder bounds the resulting quadratic error.

A zero-density estimate uniform in displacement is a separate input for bounding the weighted error as T grows.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ZetaOrdinateReflectionTransfer.actual_reflection_bound`

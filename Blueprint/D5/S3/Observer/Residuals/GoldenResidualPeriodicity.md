# Golden Residual Periodicity

## Abstract

The unforced golden residual map has only zero as a fixed or finite-period point.

**Theorem 1.1 (Unforced golden completion has no off-line fixed point).**

$$\begin{gathered}\forall \Delta: \mathbb{R}, (-\phi^{-1} \Delta = \Delta \iff \Delta = 0) \land\\{}\forall k: \mathbb{N}, k > 0 \Rightarrow \forall \Delta: \mathbb{R}, (\operatorname{iterate}({\Lambda x: \mathbb{R}, -\phi^{-1} x}, k, \Delta) = \Delta \iff \Delta = 0).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Residuals/GoldenResidualPeriodicity.unforced_golden_completion_has_no_off_line_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual update is constructed directly as multiplication by the negative reciprocal of Mathlib's real golden ratio. Its fixed-point equation holds exactly at zero.

For every positive natural period k, the k-fold iterate has multiplier the k-th power of that scalar. Its absolute value is strictly below one, so the periodic-point equation again holds exactly at zero.

## References

- Truth anchor: `D5/S3/Observer/Residuals/GoldenResidualPeriodicity.unforced_golden_completion_has_no_off_line_fixed_point`

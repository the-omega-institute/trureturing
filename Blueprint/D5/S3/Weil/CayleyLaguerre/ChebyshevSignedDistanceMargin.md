# Chebyshev Signed-Distance Margin

## Abstract

The first off-line Chebyshev slack has an exact positive separation margin.

**Theorem 1.1 (First Chebyshev Off-Line Exact Margin).**

$$\forall a, \delta: \mathbb{R},\\{}(0 < \delta) \land (\delta^{2} < a) \Rightarrow\\{}\operatorname{let} u_{off} = \frac{-\delta^{2} - a}{-\delta^{2} + a},\\{}\operatorname{let} s_{off} = 1 - T_{1}(u_{off})^{2},\\{}\operatorname{let} m = \frac{4 \times a \times \delta^{2}}{(a - \delta^{2})^{2}},\\{}(s_{off} = -m \land 0 < m).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceMargin.first_chebyshev_off_line_exact_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive delta with delta squared below the scale a, evaluating the first Chebyshev slack at the negative signed squared distance gives the negative of the displayed explicit margin.

The same hypotheses make that margin strictly positive. This is only a finite algebraic separation result; it makes no converse claim and asserts no connection to a xi spectrum.

## References

- Truth anchor: `D5/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceMargin.first_chebyshev_off_line_exact_margin`
- Dependency: [D5/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceSeparator](ChebyshevSignedDistanceSeparator.md)

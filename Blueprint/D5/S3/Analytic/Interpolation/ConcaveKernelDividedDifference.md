# Sign of a second divided difference with a localized positive part

## Abstract

Concave-kernel sign comparison for a second divided difference.

**Theorem 1.1 (Strict sign of the integral against a concave kernel).**

Lean statement: `D5/S3/Analytic/Interpolation/ConcaveKernelDividedDifference.integral_mul_concave_neg_of_lobe_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ConcaveKernelDividedDifference.integral_mul_concave_neg_of_lobe_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let left < right be the endpoints of the integration interval. The integrand h is continuous from the smaller of a and left to right and strictly negative in the interior of the integration interval outside [a,b]. Let a < b < c <= right. The continuous concave kernel k is strictly positive in the interior.

Assume that the integral of the positive part of h from a to b is strictly smaller than the integral of minus h from b to c weighted by the fraction (c-t)/(c-a). Then the integral of h times k is negative. If b is at or to the left of the integration interval, strict negativity holds pointwise in the interior. Otherwise choose a point of maximum kernel value on the portion of [a,b] inside the integration interval. That value bounds the possible positive contribution. The chord from the same point to c gives the lower bound for k on [b,c] used to control the negative contribution.

**Theorem 1.2 (Decreasing adjacent secant slopes at three distinct nodes).**

Lean statement: `D5/S3/Analytic/Interpolation/ConcaveKernelDividedDifference.three_node_slope_sub_slope_neg_of_lobe_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/ConcaveKernelDividedDifference.three_node_slope_sub_slope_neg_of_lobe_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Carl de Boor (2005). *Divided Differences*. URL: <https://arxiv.org/abs/math/0502036>.

*Commentary.*

Take three ordered distinct real nodes and a function with two derivatives on their closed span. Its second derivative must meet the continuity, sign, and weighted integral hypotheses of the preceding theorem with the first and last nodes as endpoints. The slope from the middle node to the last is strictly smaller than the slope from the first to the middle.

On the span of the nodes, the tent kernel is the minimum of the affine function rising from zero to one on the left panel and the affine function falling from one to zero on the right panel. Integrating by parts on the two panels gives the difference of the adjacent secant slopes. Division by the positive span gives the classical second divided difference in de Boor's Peano-kernel representation. The weighted comparison supplies its sign.

For the signed cutoff problem, use the strictly increasing normalized heat coordinate as the interpolation variable and take the second derivative of the selected linear combination in that variable. The sign comparison applies when the third node reaches the end of the certified negative interval. The spectral data and the lower and upper bounds for the integrals enter as hypotheses.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/ConcaveKernelDividedDifference.integral_mul_concave_neg_of_lobe_bound`
- Truth anchor: `D5/S3/Analytic/Interpolation/ConcaveKernelDividedDifference.three_node_slope_sub_slope_neg_of_lobe_bound`

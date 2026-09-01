# Ordered-Time Simplex Second-Magnus Average

## Abstract

Evaluate the ordered-simplex average of the second-Magnus kernel exactly.

**Theorem 1.1 (Exact ordered-simplex response).**

$$\forall g \in \mathbb{R}, T \in \mathbb{R},\; g \neq 0 \Rightarrow \operatorname{A}\left(g, T\right) = T^{2} - \frac{2 \times (1 - \operatorname{cos}\left(g \times T\right))}{g^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/OrderedTimeSimplexSecondMagnusAverage.ordered_time_simplex_kernel_average_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero frequency gap, collapsing the ordered two-time simplex to the time difference gives a triangularly weighted squared sine integral with an exact closed form.

The formula supplies a common finite horizon for each fixed gap. A uniform minimum over a finite frequency family and a Bochner-valued Magnus integral remain future transport steps.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/OrderedTimeSimplexSecondMagnusAverage.ordered_time_simplex_kernel_average_formula`
- Dependency: [D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature](SecondMagnusSwapCurvature.md)

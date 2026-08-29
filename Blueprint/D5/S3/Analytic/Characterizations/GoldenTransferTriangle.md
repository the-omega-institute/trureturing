# Golden Transfer Triangle

## Abstract

The sharp disk radius, inverse fixed point, local derivative, and shortest-orbit scale are all governed by the golden ratio.

**Theorem 1.1 (The golden transfer quantities agree).**

$$\operatorname{IsLUB}(\left\{r \in \mathbb{R} \mid 1 \le r \land \left(r < 2 \land \frac{1}{2 - r} < 1 + r\right)\right\}, \varphi) \land \left(\varphi - 1 = \varphi^{-1} \land \left(\left|\operatorname{deriv}(x \mapsto \frac{1}{x + 1}, \varphi - 1)\right| = \varphi^{-2} \land \operatorname{exp}(-(4 \operatorname{log}(\varphi))) = \varphi^{-4}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/GoldenTransferTriangle.golden_transfer_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source disk inequality is equivalent, on radii at least one, to the open interval ending at phi. Its least upper bound is therefore the golden ratio.

The quadratic identity for phi gives the reciprocal fixed point. Direct differentiation of x mapped to one over x plus one gives the inverse-square derivative magnitude, and four exponential-log factors give the inverse fourth power.

## References

- Truth anchor: `D5/S3/Analytic/Characterizations/GoldenTransferTriangle.golden_transfer_triangle`

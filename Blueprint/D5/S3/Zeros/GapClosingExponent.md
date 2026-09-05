# Gap-Closing Exponent

## Abstract

A nonzero leading term fixes the punctured gap-closing exponent.

**Theorem 1.1 (The normalized gap converges to its positive leading coefficient).**

$$\begin{aligned}\forall V: \mathbb{R} \to \mathbb{R}, c: \mathbb{C}, tStar: \mathbb{R}, m: \mathbb{N},\\{}0 < m \land c \neq 0 \land \operatorname{IsLittleOAt}(tStar, (t: \mathbb{R} \mapsto V\left(t\right) - \operatorname{normSq}(c) \times \operatorname{abs}(t - tStar)^{2 \times m}), (t: \mathbb{R} \mapsto \operatorname{abs}(t - tStar)^{2 \times m})) \Rightarrow \operatorname{Tendsto}((t: \mathbb{R} \mapsto \frac{V\left(t\right)}{\operatorname{abs}(t - tStar)^{2 \times m}}), \operatorname{puncturedNhds}(tStar), \operatorname{nhds}(\operatorname{normSq}(c))) \land 0 < \operatorname{normSq}(c).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GapClosingExponent.gap_closing_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the transverse coordinate. Let V have leading term equal to the squared modulus of a nonzero complex coefficient times the absolute displacement to the power 2m, with a little-o residual.

The multiplicity is positive. On the punctured neighborhood the power never vanishes, and dividing the little-o residual by it tends to zero. Hence the normalized gap tends to the strictly positive squared modulus, which records the exact visible exponent 2m.

## References

- Truth anchor: `D5/S3/Zeros/GapClosingExponent.gap_closing_exponent`

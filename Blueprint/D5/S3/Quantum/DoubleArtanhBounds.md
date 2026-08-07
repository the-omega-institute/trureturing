# Double Artanh Bounds

## Abstract

Bounds for the real inverse hyperbolic tangent on the open unit interval.

**Lemma 1.1 (Double artanh bounds).**

$$\forall u \in \mathbb{R},\quad 0<u<1 \Rightarrow \frac{u}{1+u^{2}} \le \operatorname{artanh}(u) \le \frac{u}{1-u^{2}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/DoubleArtanhBounds.double_artanh_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real u strictly between zero and one, artanh(u) is at least u/(1+u^2) and at most u/(1-u^2). In Chapter 4's contraction-spectrum analysis, these inequalities serve as the lower- and upper-bound lemma for the double-artanh contraction metric.

## References

- Truth anchor: `D5/S3/Quantum/DoubleArtanhBounds.double_artanh_bounds`

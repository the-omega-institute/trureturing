# A Regular Unit-Circle Sum Bound

## Abstract

The sum of distances from a unit complex phase to the negatives of the regular d-th roots is at most twice the cosecant of pi over twice d.

Let d be an integer at least two and let omega be exp(2 pi i / d). For a complex number z of modulus one, consider the sum of |1 + omega^y z| over y from zero to d minus one.

**Theorem 1.1 (The absolute cosine sum).**

$$\forall d \in \mathbb{N},\; \forall s \in \mathbb{R},\; (2 \le d) \Rightarrow \operatorname{Finset.sum}\left(\operatorname{Finset.range}\left(d\right), \lambda (y:\mathbb{N}) \mapsto \operatorname{abs}\left(\operatorname{Real.cos}\left(s + \frac{\operatorname{Real.pi}}{\operatorname{Nat.cast}\left(d\right)} \cdot \operatorname{Nat.cast}\left(y\right)\right)\right)\right) \le \frac{1}{\operatorname{Real.sin}\left(\frac{\operatorname{Real.pi}}{2 \cdot \operatorname{Nat.cast}\left(d\right)}\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoUnitCircleSum.abs_cos_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d at least two and every real phase s, the sum over y in Finset.range d of the absolute value of Real.cos (s + Real.pi / d * y) is bounded by the half-angle cosecant.

**Theorem 1.2 (The distance sum is bounded uniformly in the phase).**

$$\forall d\in\mathbb{N}, 2\le d\Rightarrow \forall z\in\mathbb{C}, \Vert z\Vert=1\Rightarrow \sum_{y=0}^{d-1}\Vert1+omega^{y}z\Vert\le\frac{2}{\sin(\frac{\pi}{2d})}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PeritoUnitCircleSum.unit_circle_sum_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write z as exp(2 i s). Factoring 1 + exp(2 i t) as 2 cos(t) exp(i t) shows that the distance sum is twice the sum of |cos(s + pi y / d)|.

This absolute cosine sum has period pi / d: shifting the phase cycles the sample indices, and the last sample differs from the first by pi, which preserves the absolute cosine. Reduce s modulo this period to t in [-pi/2, -pi/2 + pi/d). All d sampled angles then lie in [-pi/2, pi/2], where cosine is nonnegative.

The finite trigonometric sum identity gives the cosine sum as cos(t + (d - 1) pi / (2 d)) / sin(pi / (2 d)). The denominator is positive and cosine is at most one, giving the stated uniform bound. The same reduction applies to both odd and even values of d.

## References

- Truth anchor: `D5/S3/QuantumBounds/PeritoUnitCircleSum.abs_cos_sum_le`
- Truth anchor: `D5/S3/QuantumBounds/PeritoUnitCircleSum.unit_circle_sum_le`
- Dependency: [D5/S3/Observer/WindowRegister](../Observer/WindowRegister.md)

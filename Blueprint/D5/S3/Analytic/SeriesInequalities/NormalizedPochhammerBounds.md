# Normalized Pochhammer Bounds

## Abstract

Normalized complex Pochhammer products obey a uniform explicit disk bound.

**Definition 1.1 (Factorial normalization).**

$$\forall k \in \mathbb{N},\; \forall z \in \mathbb{C},\; P\left(k, z\right)=\frac{(-1)^{k} eval\left(descPochhammer\left(\mathbb{C}, k\right), z-1\right)}{k!}$$

*Formalization.* `D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds.normalizedPochhammer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

Here P denotes normalizedPochhammer. The descending Pochhammer polynomial evaluated at z minus one is multiplied by the kth power of minus one and divided by k factorial.

**Theorem 1.2 (The original finite product).**

$$\forall k \in \mathbb{N},\; \forall z \in \mathbb{C},\; P\left(k, z\right)=\prod_{j\in range\left(k\right)}(1-\frac{z}{j+1})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds.normalized_pochhammer_eq_prod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The normalization equals the product of one minus z divided by j plus one, over j in the range from zero through k minus one. This identity retains zero factors and all complex parameters.

**Theorem 1.3 (The zero index).**

$$\forall z \in \mathbb{C},\; P\left(0, z\right)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds.normalized_pochhammer_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

At index zero the empty product is one. The compact-majorant consumer uses this companion on its finite-prefix continuity path.

**Theorem 1.4 (An explicit disk bound).**

$$\forall R \in \mathbb{R},\; \forall k \in \mathbb{N},\; \forall z \in \mathbb{C},\; 0\le R\land 1\le k\land \left\lVert z \right\rVert\le R\Rightarrow \left\lVert P\left(k, z\right) \right\rVert\le exp\left(R+R^{2}\right) k^{-Re\left(z\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds.normalized_pochhammer_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

For every nonnegative real radius R, every natural k at least one and every complex z of norm at most R, the norm is at most exp(R + R squared) times k raised to minus the real part of z. The proof accumulates squared factors using the unrestricted scalar exponential inequality. Harmonic and finite inverse-square bounds control the error without a sign restriction on the real part. The explicit constant and closed disk are repo-derived refinements of the source's unspecified open-disk constant, not a literal source statement. These general analytic and algebraic results have utility kind none; they are not bounded computations or certified finite instances.

## References

- Truth anchor: `D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds.normalizedPochhammer`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds.normalized_pochhammer_eq_prod`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds.normalized_pochhammer_norm_le`
- Truth anchor: `D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds.normalized_pochhammer_zero`

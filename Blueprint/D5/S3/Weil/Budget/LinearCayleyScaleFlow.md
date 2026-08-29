# Linear Cayley Scale Flow

## Abstract

The canonical logarithmic Cayley flow has a transport-decay generator and invariant characteristics.

**Definition 1.1 (Cayley characteristic).**

$$\forall u: \mathbb{C}, tau: \mathbb{R}, \operatorname{chi}\left(u, tau\right) = \operatorname{Phi}\left(\operatorname{tanh}\left(- \frac{tau}{2}\right), u\right).$$

*Formalization.* `D5/S3/Weil/Budget/LinearCayleyScaleFlow.cayleyCharacteristic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The characteristic is the imported real disk automorphism with the negative half-time hyperbolic parameter.

**Definition 1.2 (Disk artanh branch).**

$$\forall w: \mathbb{C}, \operatorname{diskArtanh}\left(w\right) = \frac{\operatorname{log}\left(1 + w\right) - \operatorname{log}\left(1 - w\right)}{2}.$$

*Formalization.* `D5/S3/Weil/Budget/LinearCayleyScaleFlow.diskArtanh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This half-log expression fixes the analytic branch on the complex unit disk.

**Theorem 1.3 (Linear Cayley scale PDE).**

$$\forall nu: \operatorname{Measure}\left(\mathbb{R}\right), tau: \mathbb{R}, w, u: \mathbb{C},\\{}\operatorname{map}\left(x \mapsto - x, nu\right) = nu \land\\{}{\forall a: \mathbb{R}, 0 < a \Rightarrow \operatorname{FiniteMeasure}\left(W_{a}(nu)\right)} \land\\{}\left\lVert w \right\rVert < 1 \land \left\lVert u \right\rVert < 1 \Rightarrow\\{}{\operatorname{HasDerivAt}\left(t \mapsto \operatorname{F}\left(\operatorname{exp}\left(t\right), nu, w\right), \frac{1 - w^{2}}{2} \cdot \operatorname{deriv}\left(w \mapsto \operatorname{F}\left(\operatorname{exp}\left(tau\right), nu, w\right), w\right) - \operatorname{F}\left(\operatorname{exp}\left(tau\right), nu, w\right), tau\right)} \land\\{}{\operatorname{HasDerivAt}\left(t \mapsto \operatorname{chi}\left(u, t\right), - \frac{1 - \operatorname{chi}\left(u, tau\right)^{2}}{2}, tau\right)} \land\\{}{\operatorname{HasDerivAt}\left(t \mapsto \operatorname{diskArtanh}\left(\operatorname{chi}\left(u, t\right)\right) + \frac{\operatorname{ofReal}\left(t\right)}{2}, 0, tau\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/LinearCayleyScaleFlow.linear_cayley_scale_pde` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiation under the finite resolvent integral supplies the spatial derivative. The imported finite scale-covariance law then gives the time generator, while the explicit characteristic makes the disk-artanh coordinate invariant.

## References

- Truth anchor: `D5/S3/Weil/Budget/LinearCayleyScaleFlow.cayleyCharacteristic`
- Truth anchor: `D5/S3/Weil/Budget/LinearCayleyScaleFlow.diskArtanh`
- Truth anchor: `D5/S3/Weil/Budget/LinearCayleyScaleFlow.linear_cayley_scale_pde`
- Dependency: [D5/S3/Weil/Budget/CaratheodoryScaleCovariance](CaratheodoryScaleCovariance.md)

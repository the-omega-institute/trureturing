# Caratheodory Scale Covariance

## Abstract

Even resolvent spectra give covariant Caratheodory functions and budgets.

**Definition 1.1 (Caratheodory kernel).**

$$\forall z, w: \mathbb{C}, \operatorname{K}\left(z, w\right) = \frac{z + w}{z - w}.$$

*Formalization.* `D5/S3/Weil/Budget/CaratheodoryScaleCovariance.caratheodoryKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel is constructed directly from the two complex variables.

**Definition 1.2 (Caratheodory function).**

$$\forall nu: \operatorname{Measure}\left(\mathbb{R}\right), a: \mathbb{R}, w: \mathbb{C}, F_{a}(nu, w) = \operatorname{integral}\left(mu_{a}(nu), z \mapsto \operatorname{K}\left(z, w\right)\right).$$

*Formalization.* `D5/S3/Weil/Budget/CaratheodoryScaleCovariance.caratheodoryFunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function integrates the kernel against the imported Cayley spectral measure.

**Definition 1.3 (Observer scale parameter).**

$$\forall a, b: \mathbb{R}, s_{a,b} = \frac{b - a}{a + b}.$$

*Formalization.* `D5/S3/Weil/Budget/CaratheodoryScaleCovariance.observerScaleParameter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This parameter is the observer-side sign convention for the real disk automorphism.

**Definition 1.4 (Resolvent budget).**

$$\forall nu: \operatorname{Measure}\left(\mathbb{R}\right), a: \mathbb{R}, R_{a}(nu) = \operatorname{toReal}\left(\operatorname{mass}\left(W_{a}(nu)\right)\right).$$

*Formalization.* `D5/S3/Weil/Budget/CaratheodoryScaleCovariance.resolventBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The budget is the real total mass of the resolvent-weighted source measure.

**Theorem 1.5 (Caratheodory scale covariance).**

$$\forall nu: \operatorname{Measure}\left(\mathbb{R}\right), a, b: \mathbb{R}, w: \mathbb{C},\\{}0 < a \land 0 < b \land \operatorname{map}\left(x \mapsto - x, nu\right) = nu \land\\{}\operatorname{FiniteMeasure}\left(W_{a}(nu)\right) \land \operatorname{FiniteMeasure}\left(W_{b}(nu)\right) \land \left\lVert w \right\rVert < 1 \Rightarrow\\{}{F_{b}(nu, w) = \operatorname{ofReal}\left(\frac{a}{b}\right) \cdot F_{a}(nu, Phi_{s_{a,b}}(w))} \land\\{}{\operatorname{ofReal}\left(R_{b}(nu)\right) = \operatorname{ofReal}\left(\frac{a}{b}\right) \cdot F_{a}(nu, \operatorname{ofReal}\left(s_{a,b}\right))}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/CaratheodoryScaleCovariance.caratheodory_scale_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evenness cancels the imaginary normalization term after pairing the positive and negative spectral points. Evaluating the same law at zero gives the budget specialization.

## References

- Truth anchor: `D5/S3/Weil/Budget/CaratheodoryScaleCovariance.caratheodoryFunction`
- Truth anchor: `D5/S3/Weil/Budget/CaratheodoryScaleCovariance.caratheodoryKernel`
- Truth anchor: `D5/S3/Weil/Budget/CaratheodoryScaleCovariance.caratheodory_scale_covariance`
- Truth anchor: `D5/S3/Weil/Budget/CaratheodoryScaleCovariance.observerScaleParameter`
- Truth anchor: `D5/S3/Weil/Budget/CaratheodoryScaleCovariance.resolventBudget`
- Dependency: [D5/S3/Weil/Budget/PositiveCayleyScaleTransport](PositiveCayleyScaleTransport.md)

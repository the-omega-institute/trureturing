# Full Circle Primal Attainment

## Abstract

Every feasible budgeted continuous moment problem on the unit circle attains its largest dominated normalized-Haar coefficient.

**Definition 1.1 (Normalized Haar measure on the unit circle).**

$$m_{T}: \operatorname{FiniteMeasure}(Circle) = \operatorname{map}(\operatorname{homeomorphCircle}', \operatorname{haarAddCircle}(\operatorname{AddCircle}(2 \cdot \pi))).$$

*Formalization.* `D5/S3/Weil/Budget/FullCirclePrimalAttainment.normalizedCircleHaar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The measure is constructed on the exact complex unit circle by pushing the normalized additive-circle Haar probability measure through the canonical homeomorphism.

**Theorem 1.2 (Normalized circle Haar has unit mass).**

$$\operatorname{mass}(m_{T}) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/FullCirclePrimalAttainment.normalizedCircleHaar_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Measure preservation under the circle homeomorphism carries the unit mass of normalized additive Haar to the complex unit circle.

**Theorem 1.3 (A feasible circle primal attains its maximal Haar floor).**

$$\forall iota: \operatorname{Type}, Gamma: iota \to \operatorname{ContinuousMap}(Circle, \mathbb{R}), w: iota \to \mathbb{R},\\{}C: \mathbb{R}_{\geq0}, (\exists \mu: \operatorname{FiniteMeasure}(Circle), \operatorname{mass}(\mu) \leq C \land (\forall i: iota, \int_{Circle} Gamma(i)(z) \mathrm{d}\mu = w(i))) \Rightarrow\\{}\exists \mu: \operatorname{FiniteMeasure}(Circle), \operatorname{mass}(\mu) \leq C \land\\{}(\forall i: iota, \int_{Circle} Gamma(i)(z) \mathrm{d}\mu = w(i)) \land\\{}\exists \alpha: \mathbb{R}_{\geq0}, \alpha \cdot m_{T} \leq \mu \land\\{}\forall \nu: \operatorname{FiniteMeasure}(Circle), \operatorname{mass}(\nu) \leq C \Rightarrow\\{}(\forall i: iota, \int_{Circle} Gamma(i)(z) \mathrm{d}\nu = w(i)) \Rightarrow\\{}\forall \beta: \mathbb{R}_{\geq0}, \beta \cdot m_{T} \leq \nu \Rightarrow \beta \leq \alpha.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/FullCirclePrimalAttainment.full_circle_primal_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The premise displays the budget and every continuous circle-moment constraint. The conclusion returns a feasible measure and an actually dominated normalized-Haar coefficient.

The final universal comparison quantifies over every feasible measure and every Haar coefficient it dominates, so the selected coefficient is attained and globally maximal.

Compactness is applied to pairs consisting of the Haar coefficient and a residual positive finite measure. Measure subtraction converts any competing domination inequality into such a pair.

## References

- Truth anchor: `D5/S3/Weil/Budget/FullCirclePrimalAttainment.full_circle_primal_attainment`
- Truth anchor: `D5/S3/Weil/Budget/FullCirclePrimalAttainment.normalizedCircleHaar`
- Truth anchor: `D5/S3/Weil/Budget/FullCirclePrimalAttainment.normalizedCircleHaar_mass`

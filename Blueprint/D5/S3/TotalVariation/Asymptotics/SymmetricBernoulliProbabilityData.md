# Symmetric Bernoulli Probability Data

## Abstract

The symmetric Bernoulli bias laws have unit mass at every real bias and are nonnegative on the closed probability range.

Both laws are mass functions on Bool. The function positiveBiasLaw delta sends true to one half plus delta and false to one half minus delta. The function negativeBiasLaw delta reverses those two masses.

The value here is API, not mathematical novelty. At the component level, the unit-mass proofs evaluate the two-point sum directly, and the nonnegativity proofs are a case split on Bool plus one linear arithmetic step; the bundled theorem only pairs the four component results.

SymmetricBernoulliSecondOrder and FourLocalEvidenceClosedForms carry byte-identical private copies of the bundled statement. The second module imports the first. Both modules are frozen, so neither can import this module, and this change removes neither private copy.

This module has zero consumers today. It does not prevent another future copy; what it adds is an available public name. The private copies assume the strict range |delta| < 1/2. In contrast, unit mass needs no hypothesis, while nonnegativity needs only the closed range |delta| <= 1/2. Separating the components makes those bounds visible.

**Theorem 1.1 (The positive-bias law has unit mass at every real bias).**

$$\forall \delta: \mathbb{R}, \sum_{b \in Bool} \operatorname{positiveBiasLaw}\left(\delta\right)(b) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData.positiveBiasLaw_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real delta, including values outside the probability range, the two positive-bias masses add to one. No bound on delta is used.

**Theorem 1.2 (The negative-bias law has unit mass at every real bias).**

$$\forall \delta: \mathbb{R}, \sum_{b \in Bool} \operatorname{negativeBiasLaw}\left(\delta\right)(b) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData.negativeBiasLaw_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real delta, the reversed pair of masses also adds to one. This normalization identity likewise has no bias hypothesis.

**Theorem 1.3 (The positive-bias law is nonnegative on the closed bias range).**

$$\forall \delta: \mathbb{R}, \left|\delta\right| \leq \frac{1}{2} \Rightarrow \forall b: Bool, 0 \leq \operatorname{positiveBiasLaw}\left(\delta\right)(b).$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData.positiveBiasLaw_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If |delta| <= 1/2, both values of positiveBiasLaw delta are nonnegative. Equality is permitted, so this includes either endpoint.

**Theorem 1.4 (The negative-bias law is nonnegative on the closed bias range).**

$$\forall \delta: \mathbb{R}, \left|\delta\right| \leq \frac{1}{2} \Rightarrow \forall b: Bool, 0 \leq \operatorname{negativeBiasLaw}\left(\delta\right)(b).$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData.negativeBiasLaw_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same closed bound |delta| <= 1/2, reversing the two masses preserves pointwise nonnegativity on Bool.

**Theorem 1.5 (Both bias laws are probability data on the closed bias range).**

$$\begin{aligned}\forall \delta: \mathbb{R}, \left|\delta\right| \leq \frac{1}{2} \Rightarrow\\((\forall b: Bool, 0 \leq \operatorname{positiveBiasLaw}\left(\delta\right)(b)) \land \sum_{b \in Bool} \operatorname{positiveBiasLaw}\left(\delta\right)(b) = 1) \land\\((\forall b: Bool, 0 \leq \operatorname{negativeBiasLaw}\left(\delta\right)(b)) \land \sum_{b \in Bool} \operatorname{negativeBiasLaw}\left(\delta\right)(b) = 1).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData.bias_laws_probability_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On |delta| <= 1/2, the positive law's pointwise nonnegativity and unit mass are paired first. The corresponding negative-law pair follows, and the theorem conjoins those two pairs in that order.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData.bias_laws_probability_data`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData.negativeBiasLaw_nonneg`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData.negativeBiasLaw_sum`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData.positiveBiasLaw_nonneg`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliProbabilityData.positiveBiasLaw_sum`
- Dependency: [D5/S3/TotalVariation/Asymptotics/SymmetricBernoulliSecondOrder](SymmetricBernoulliSecondOrder.md)

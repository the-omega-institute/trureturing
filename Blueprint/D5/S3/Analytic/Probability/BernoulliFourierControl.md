# Bernoulli Fourier Control

## Abstract

Variance-weighted Fourier estimates control Bernoulli products.

**Definition 1.1 (bernoulliVariance).**

$$\forall (p: \mathbb{R}), \operatorname{bernoulliVariance}\left(p\right) = p \cdot \left(1 - p\right)$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliVariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The variance of a Bernoulli variable with success parameter p.

**Definition 1.2 (centeredBernoulli).**

$$\forall (p: \mathbb{R}), \forall (s: \mathbb{R}), \operatorname{centeredBernoulli}\left(p, s\right) = (1 - p: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{exp}\left((-(s) \cdot p: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right) + (p: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{exp}\left((s \cdot \left(1 - p\right): \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right)$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliFourierControl.centeredBernoulli` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The characteristic function of the centered Bernoulli variable. Real coefficients and phases are coerced into the complex numbers.

**Theorem 1.3 (centered_bernoulli_product_gaussian_error).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \mathbb{R}), \forall (u: \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(m\right)), (0 \le p\left(i\right)) \land (p\left(i\right) \le 1)) \land (0 < \sum_{j: \operatorname{Fin}\left(m\right)} (\operatorname{bernoulliVariance}\left(p\left(j\right)\right)))) \Rightarrow (\left\lVert \prod_{i: \operatorname{Fin}\left(m\right)} (\operatorname{centeredBernoulli}\left(p\left(i\right), \frac{u}{\operatorname{Real}.\operatorname{sqrt}\left(\sum_{j: \operatorname{Fin}\left(m\right)} (\operatorname{bernoulliVariance}\left(p\left(j\right)\right))\right)}\right)) - (\operatorname{Real}.\operatorname{exp}\left(\frac{-((u)^{2})}{2}\right): \mathbb{C}) \right\rVert \le \frac{(\left|u\right|)^{3}}{6 \cdot \operatorname{Real}.\operatorname{sqrt}\left(\sum_{j: \operatorname{Fin}\left(m\right)} (\operatorname{bernoulliVariance}\left(p\left(j\right)\right))\right)} + \frac{(u)^{4}}{32 \cdot \sum_{j: \operatorname{Fin}\left(m\right)} (\operatorname{bernoulliVariance}\left(p\left(j\right)\right))})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliFourierControl.centered_bernoulli_product_gaussian_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The summed third-moment remainder and the Gaussian factor remainder give a variance-weighted bound uniform in the Bernoulli parameters.

**Theorem 1.4 (centered_bernoulli_charFun_tendsto).**

$$\forall (m: \mathbb{N} \to \mathbb{N}), \forall (p: \forall (n: \mathbb{N}), \operatorname{Fin}\left(m\left(n\right)\right) \to \mathbb{R}), \forall (V: \mathbb{N} \to \mathbb{R}), \forall (u: \mathbb{R}), ((\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto (\forall (i: \operatorname{Fin}\left(m\left(n\right)\right)), (0 \le p\left(n, i\right)) \land (p\left(n, i\right) \le 1)) \land ((V\left(n\right) = \sum_{i: \operatorname{Fin}\left(m\left(n\right)\right)} (\operatorname{bernoulliVariance}\left(p\left(n, i\right)\right))) \land (0 < V\left(n\right)))), atTop\right)) \land ((\operatorname{Tendsto}\left(V, atTop, atTop\right)) \land (\forall (n: \mathbb{N}), V\left(n\right) = \sum_{i: \operatorname{Fin}\left(m\left(n\right)\right)} (\operatorname{bernoulliVariance}\left(p\left(n, i\right)\right))))) \Rightarrow (\operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \prod_{i: \operatorname{Fin}\left(m\left(n\right)\right)} (\operatorname{centeredBernoulli}\left(p\left(n, i\right), \frac{u}{\operatorname{Real}.\operatorname{sqrt}\left(V\left(n\right)\right)}\right))), atTop, \operatorname{nhds}\left((\operatorname{Real}.\operatorname{exp}\left(\frac{-((u)^{2})}{2}\right): \mathbb{C})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliFourierControl.centered_bernoulli_charFun_tendsto` (`✓ std3`). ∎

*Citation.* Edward A. Bender (1973). *Central and local limit theorems applied to asymptotic enumeration*. DOI: [10.1016/0097-3165(73)90038-1](https://doi.org/10.1016/0097-3165(73)90038-1). URL: <https://doi.org/10.1016/0097-3165(73)90038-1>.

*Commentary.*

Divergence of row variances gives the standard Gaussian characteristic function at each fixed frequency.

**Lemma 1.5 (centeredBernoulli_eq_phase).**

$$\forall (p: \mathbb{R}), \forall (s: \mathbb{R}), \operatorname{centeredBernoulli}\left(p, s\right) = \operatorname{Complex}.\operatorname{exp}\left((-(s) \cdot p: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right) \cdot \left((1 - p: \mathbb{C}) + (p: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{exp}\left((s: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliFourierControl.centeredBernoulli_eq_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Centering factors the characteristic function into a phase and the uncentered Bernoulli characteristic function.

**Theorem 1.6 (normalized_bernoulli_product_envelope).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \mathbb{R}), \forall (V: \mathbb{R}), \forall (u: \mathbb{R}), ((0 < V) \land ((V = \sum_{j: \operatorname{Fin}\left(m\right)} (\operatorname{bernoulliVariance}\left(p\left(j\right)\right))) \land (\left|u\right| \le \operatorname{Real}.\operatorname{pi} \cdot \operatorname{Real}.\operatorname{sqrt}\left(V\right)))) \Rightarrow (\left\lVert \prod_{i: \operatorname{Fin}\left(m\right)} (\operatorname{centeredBernoulli}\left(p\left(i\right), \frac{u}{\operatorname{Real}.\operatorname{sqrt}\left(V\right)}\right)) \right\rVert \le \operatorname{Real}.\operatorname{exp}\left(\frac{-(2 \cdot (u)^{2})}{(\operatorname{Real}.\operatorname{pi})^{2}}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliFourierControl.normalized_bernoulli_product_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the principal frequency interval, the normalized product is bounded by exp(-2u^2/pi^2), an integrable envelope independent of the row.

**Definition 1.7 (bernoulliWeight).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), \forall (x: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}), \operatorname{bernoulliWeight}\left(p, x\right) = \prod_{i: \operatorname{Fin}\left(m\right)} (\operatorname{ite}\left(x\left(i\right) = true, (p\left(i\right): \mathbb{R}), 1 - (p\left(i\right): \mathbb{R})\right))$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The atom weight is the product of p(i) for true coordinates and 1-p(i) for false coordinates. The conditional tests whether x(i) is true.

**Definition 1.8 (bernoulliSpace).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), \operatorname{bernoulliSpace}\left(p\right) = \operatorname{Measure}.\operatorname{pi}\left((i: \operatorname{Fin}\left(m\right) \mapsto \operatorname{bernoulliMeasure}\left(true, false, p\left(i\right)\right))\right)$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The probability space is the product of the two-point measures bernoulliMeasure true false p(i).

**Definition 1.9 (bernoulliSpaceProbability).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), \operatorname{IsProbabilityMeasure}\left(\operatorname{bernoulliSpace}\left(p\right)\right)$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliSpaceProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of the Bernoulli probability measures is a probability measure.

**Lemma 1.10 (bernoulli_atom).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), \forall (x: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}), \operatorname{Measure}.\operatorname{real}\left(\operatorname{bernoulliSpace}\left(p\right), \left\{x\right\}\right) = \operatorname{bernoulliWeight}\left(p, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulli_atom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real measure of a singleton is its product weight.

## References

- Truth anchor: `D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliSpace`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliSpaceProbability`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliVariance`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliWeight`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulli_atom`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliFourierControl.centeredBernoulli`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliFourierControl.centeredBernoulli_eq_phase`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliFourierControl.centered_bernoulli_charFun_tendsto`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliFourierControl.centered_bernoulli_product_gaussian_error`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliFourierControl.normalized_bernoulli_product_envelope`
- Dependency: [D5/S3/Zeros/Endpoints/BernoulliBridgeVariance](../../Zeros/Endpoints/BernoulliBridgeVariance.md)

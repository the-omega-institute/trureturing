# Uniform CDFConvergence

## Abstract

Pointwise convergence to a continuous distribution function implies uniform convergence.

**Theorem 1.1 (monotone_cdf_pointwise_to_uniform).**

$$\forall (F: \mathbb{N} \to \left(\mathbb{R} \to \mathbb{R}\right)), \forall (G: \mathbb{R} \to \mathbb{R}), ((\forall (n: \mathbb{N}), \operatorname{Monotone}\left(F\left(n\right)\right)) \land ((\operatorname{Monotone}\left(G\right)) \land ((\operatorname{Continuous}\left(G\right)) \land ((\forall (n: \mathbb{N}), \forall (x: \mathbb{R}), 0 \le F\left(n, x\right)) \land ((\forall (n: \mathbb{N}), \forall (x: \mathbb{R}), F\left(n, x\right) \le 1) \land ((\forall (x: \mathbb{R}), 0 \le G\left(x\right)) \land ((\forall (x: \mathbb{R}), G\left(x\right) \le 1) \land ((\operatorname{Tendsto}\left(G, atBot, \operatorname{nhds}\left(0\right)\right)) \land ((\operatorname{Tendsto}\left(G, atTop, \operatorname{nhds}\left(1\right)\right)) \land (\forall (x: \mathbb{R}), \operatorname{Tendsto}\left((n: \mathbb{N} \mapsto F\left(n, x\right)), atTop, \operatorname{nhds}\left(G\left(x\right)\right)\right))))))))))) \Rightarrow (\forall (e: \mathbb{R}), (0 < e) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \forall (x: \mathbb{R}), \left|F\left(n, x\right) - G\left(x\right)\right| < e), atTop\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformCDFConvergence.monotone_cdf_pointwise_to_uniform` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

Monotone distribution functions converging pointwise to a continuous distribution function converge uniformly on the whole real line. The proof uses a finite compact cover and the two limiting tails. See Durrett, Exercise 3.2.9.

**Lemma 1.2 (gaussian_charFun_standard).**

$$\forall (u: \mathbb{R}), \operatorname{charFun}\left(\operatorname{gaussianReal}\left(0, 1\right), u\right) = (\operatorname{Real}.\operatorname{exp}\left(\frac{-u^{2}}{2}\right): \mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformCDFConvergence.gaussian_charFun_standard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The characteristic function of the standard Gaussian at a real frequency u is exp(-u^2/2).

**Lemma 1.3 (gaussian_factor_norm_le).**

$$\forall (v: \mathbb{R}), \forall (s: \mathbb{R}), (0 \le v) \Rightarrow (\left\lVert (\operatorname{Real}.\operatorname{exp}\left(\frac{-s^{2} \cdot v}{2}\right): \mathbb{C}) \right\rVert \le 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformCDFConvergence.gaussian_factor_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A Gaussian factor with nonnegative variance has complex norm at most one at every real frequency.

**Theorem 1.4 (charFun_limit_uniform_gaussian_cdf).**

$$\forall (M: \mathbb{N} \to \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right)), (\forall (u: \mathbb{R}), \operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \operatorname{charFun}\left((M\left(n\right): \operatorname{Measure}\left(\mathbb{R}\right)), u\right)), atTop, \operatorname{nhds}\left((\operatorname{Real}.\operatorname{exp}\left(\frac{-((u)^{2})}{2}\right): \mathbb{C})\right)\right)) \Rightarrow (\forall (e: \mathbb{R}), (0 < e) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \forall (t: \mathbb{R}), \left|\operatorname{cdf}\left((M\left(n\right): \operatorname{Measure}\left(\mathbb{R}\right)), t\right) - \operatorname{cdf}\left(\operatorname{gaussianReal}\left(0, 1\right)\right)\left(t\right)\right| < e), atTop\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformCDFConvergence.charFun_limit_uniform_gaussian_cdf` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

Convergence of the characteristic functions to the standard Gaussian characteristic function gives uniform convergence of the cumulative distribution functions. The Gaussian CDF is Mathlib cdf (gaussianReal 0 1). Lévy continuity is combined with the uniform-CDF result of Durrett, Exercise 3.2.9.

**Definition 1.5 (centeredBernoulli).**

$$\forall (p: \mathbb{R}), \forall (s: \mathbb{R}), \operatorname{centeredBernoulli}\left(p, s\right) = (1 - p: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{exp}\left((-(s) \cdot p: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right) + (p: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{exp}\left((s \cdot \left(1 - p\right): \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right)$$

*Formalization.* `D5/S3/Analytic/Probability/UniformCDFConvergence.centeredBernoulli` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The characteristic function of the centered Bernoulli variable. Real coefficients and phases are coerced into the complex numbers.

**Theorem 1.6 (centered_bernoulli_charFun_tendsto).**

$$\forall (m: \mathbb{N} \to \mathbb{N}), \forall (p: \forall (n: \mathbb{N}), \operatorname{Fin}\left(m\left(n\right)\right) \to \mathbb{R}), \forall (V: \mathbb{N} \to \mathbb{R}), \forall (u: \mathbb{R}), ((\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto (\forall (i: \operatorname{Fin}\left(m\left(n\right)\right)), (0 \le p\left(n, i\right)) \land (p\left(n, i\right) \le 1)) \land ((V\left(n\right) = \sum_{i: \operatorname{Fin}\left(m\left(n\right)\right)} (p\left(n, i\right) \cdot (1 - p\left(n, i\right)))) \land (0 < V\left(n\right)))), atTop\right)) \land ((\operatorname{Tendsto}\left(V, atTop, atTop\right)) \land (\forall (n: \mathbb{N}), V\left(n\right) = \sum_{i: \operatorname{Fin}\left(m\left(n\right)\right)} (p\left(n, i\right) \cdot (1 - p\left(n, i\right)))))) \Rightarrow (\operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \prod_{i: \operatorname{Fin}\left(m\left(n\right)\right)} (\operatorname{centeredBernoulli}\left(p\left(n, i\right), \frac{u}{\operatorname{Real}.\operatorname{sqrt}\left(V\left(n\right)\right)}\right))), atTop, \operatorname{nhds}\left((\operatorname{Real}.\operatorname{exp}\left(\frac{-((u)^{2})}{2}\right): \mathbb{C})\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformCDFConvergence.centered_bernoulli_charFun_tendsto` (`✓ std3`). ∎

*Citation.* Edward A. Bender (1973). *Central and local limit theorems applied to asymptotic enumeration*. DOI: [10.1016/0097-3165(73)90038-1](https://doi.org/10.1016/0097-3165(73)90038-1). URL: <https://doi.org/10.1016/0097-3165(73)90038-1>.

*Commentary.*

Divergence of row variances gives the standard Gaussian characteristic function at each fixed frequency.

**Lemma 1.7 (centeredBernoulli_eq_phase).**

$$\forall (p: \mathbb{R}), \forall (s: \mathbb{R}), \operatorname{centeredBernoulli}\left(p, s\right) = \operatorname{Complex}.\operatorname{exp}\left((-(s) \cdot p: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right) \cdot \left((1 - p: \mathbb{C}) + (p: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{exp}\left((s: \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformCDFConvergence.centeredBernoulli_eq_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Centering factors the characteristic function into a phase and the uncentered Bernoulli characteristic function.

**Theorem 1.8 (normalized_bernoulli_product_envelope).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \mathbb{R}), \forall (V: \mathbb{R}), \forall (u: \mathbb{R}), ((0 < V) \land ((V = \sum_{j: \operatorname{Fin}\left(m\right)} (p\left(j\right) \cdot (1 - p\left(j\right)))) \land (\left|u\right| \le \operatorname{Real}.\operatorname{pi} \cdot \operatorname{Real}.\operatorname{sqrt}\left(V\right)))) \Rightarrow (\left\lVert \prod_{i: \operatorname{Fin}\left(m\right)} (\operatorname{centeredBernoulli}\left(p\left(i\right), \frac{u}{\operatorname{Real}.\operatorname{sqrt}\left(V\right)}\right)) \right\rVert \le \operatorname{Real}.\operatorname{exp}\left(\frac{-(2 \cdot (u)^{2})}{(\operatorname{Real}.\operatorname{pi})^{2}}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformCDFConvergence.normalized_bernoulli_product_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the principal frequency interval, the normalized product is bounded by exp(-2u^2/pi^2), an integrable envelope independent of the row.

**Definition 1.9 (bernoulliWeight).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), \forall (x: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}), \operatorname{bernoulliWeight}\left(p, x\right) = \prod_{i: \operatorname{Fin}\left(m\right)} (\operatorname{ite}\left(x\left(i\right) = true, (p\left(i\right): \mathbb{R}), 1 - (p\left(i\right): \mathbb{R})\right))$$

*Formalization.* `D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulliWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The atom weight is the product of p(i) for true coordinates and 1-p(i) for false coordinates. The conditional tests whether x(i) is true.

**Definition 1.10 (bernoulliSpace).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), \operatorname{bernoulliSpace}\left(p\right) = \operatorname{Measure}.\operatorname{pi}\left((i: \operatorname{Fin}\left(m\right) \mapsto \operatorname{bernoulliMeasure}\left(true, false, p\left(i\right)\right))\right)$$

*Formalization.* `D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulliSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The probability space is the product of the two-point measures bernoulliMeasure true false p(i).

**Definition 1.11 (bernoulliSpaceProbability).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), \operatorname{IsProbabilityMeasure}\left(\operatorname{bernoulliSpace}\left(p\right)\right)$$

*Formalization.* `D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulliSpaceProbability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product of the Bernoulli probability measures is a probability measure.

**Lemma 1.12 (bernoulli_atom).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), \forall (x: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}), \operatorname{Measure}.\operatorname{real}\left(\operatorname{bernoulliSpace}\left(p\right), \left\{x\right\}\right) = \operatorname{bernoulliWeight}\left(p, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulli_atom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real measure of a singleton is its product weight.

## References

- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulliSpace`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulliSpaceProbability`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulliWeight`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulli_atom`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.centeredBernoulli`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.centeredBernoulli_eq_phase`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.centered_bernoulli_charFun_tendsto`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.charFun_limit_uniform_gaussian_cdf`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.gaussian_charFun_standard`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.gaussian_factor_norm_le`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.monotone_cdf_pointwise_to_uniform`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.normalized_bernoulli_product_envelope`
- Dependency: [D5/S3/Zeros/Endpoints/BernoulliBridgeVariance](../../Zeros/Endpoints/BernoulliBridgeVariance.md)

# Uniform CDFConvergence

## Abstract

Pointwise convergence to a continuous distribution function implies uniform convergence.

**Theorem 1.1 (monotone_cdf_pointwise_to_uniform).**

$$\forall (F: \mathbb{N} \to \left(\mathbb{R} \to \mathbb{R}\right)), \forall (G: \mathbb{R} \to \mathbb{R}), ((\forall (n: \mathbb{N}), \operatorname{Monotone}\left(F\left(n\right)\right)) \land ((\operatorname{Monotone}\left(G\right)) \land ((\operatorname{Continuous}\left(G\right)) \land ((\forall (n: \mathbb{N}), \forall (x: \mathbb{R}), 0 \le F\left(n, x\right)) \land ((\forall (n: \mathbb{N}), \forall (x: \mathbb{R}), F\left(n, x\right) \le 1) \land ((\forall (x: \mathbb{R}), 0 \le G\left(x\right)) \land ((\forall (x: \mathbb{R}), G\left(x\right) \le 1) \land ((\operatorname{Tendsto}\left(G, atBot, \operatorname{nhds}\left(0\right)\right)) \land ((\operatorname{Tendsto}\left(G, atTop, \operatorname{nhds}\left(1\right)\right)) \land (\forall (x: \mathbb{R}), \operatorname{Tendsto}\left((n: \mathbb{N} \mapsto F\left(n, x\right)), atTop, \operatorname{nhds}\left(G\left(x\right)\right)\right))))))))))) \Rightarrow (\forall (e: \mathbb{R}), (0 < e) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \forall (x: \mathbb{R}), \left|F\left(n, x\right) - G\left(x\right)\right| < e), atTop\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformCDFConvergence.monotone_cdf_pointwise_to_uniform` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

Monotone distribution functions converging pointwise to a continuous distribution function converge uniformly on the whole real line. The proof uses a finite compact cover and the two limiting tails. See Durrett, Exercise 3.2.9.

**Theorem 1.2 (charFun_limit_uniform_gaussian_cdf).**

$$\forall (M: \mathbb{N} \to \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right)), (\forall (u: \mathbb{R}), \operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \operatorname{charFun}\left((M\left(n\right): \operatorname{Measure}\left(\mathbb{R}\right)), u\right)), atTop, \operatorname{nhds}\left((\operatorname{Real}.\operatorname{exp}\left(\frac{-((u)^{2})}{2}\right): \mathbb{C})\right)\right)) \Rightarrow (\forall (e: \mathbb{R}), (0 < e) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \forall (t: \mathbb{R}), \left|\operatorname{cdf}\left((M\left(n\right): \operatorname{Measure}\left(\mathbb{R}\right)), t\right) - \operatorname{cdf}\left(\operatorname{gaussianReal}\left(0, 1\right)\right)\left(t\right)\right| < e), atTop\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/UniformCDFConvergence.charFun_limit_uniform_gaussian_cdf` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

Convergence of the characteristic functions to the standard Gaussian characteristic function gives uniform convergence of the cumulative distribution functions. The Gaussian CDF is Mathlib cdf (gaussianReal 0 1). Lévy continuity is combined with the uniform-CDF result of Durrett, Exercise 3.2.9.

## References

- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.charFun_limit_uniform_gaussian_cdf`
- Truth anchor: `D5/S3/Analytic/Probability/UniformCDFConvergence.monotone_cdf_pointwise_to_uniform`

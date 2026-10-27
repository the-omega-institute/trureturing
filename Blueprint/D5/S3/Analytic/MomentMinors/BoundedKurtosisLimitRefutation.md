# A counterexample to the two-sided kurtosis limits

## Abstract

A three-point probability law exceeds the proposed two-sided kurtosis upper limit.

**Definition 1.1 (The two-point kurtosis expression).**

$$\forall \left(\delta: \mathbb{R}\right), \left(\forall \left(\delta{m}: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Analytic.MomentMinors.BoundedKurtosisLimitRefutation.kurtosisBound}\left(\delta, \delta{m}\right): \mathbb{R}\right) = \left(\left(\left(\frac{\delta}{\delta{m}}\right) - \left(\frac{\delta{m}}{\delta}\right)\right)^{\left(2: \mathbb{N}\right)}\right) + \left(\left(1: \mathbb{R}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.kurtosisBound` (`✓ std3`).

*Citation.* David J. Meer; Eric R. Weeks (2024). *Bounded distributions place limits on skewness and larger moments*. DOI: [10.1371/journal.pone.0297862](https://doi.org/10.1371/journal.pone.0297862). URL: <https://arxiv.org/abs/2308.05006v2>.

*Commentary.*

For real δ and δm, kurtosisBound is (δ/δm − δm/δ)² + 1. This is the expression D₄,ₘ(δ) in Meer and Weeks, arXiv:2308.05006v2, plos_latex_template.tex, lines 451–456. The real-valued definition also includes zero arguments, using real division with inverse zero equal to zero.

**Definition 1.2 (The proposed limits for bounded probability laws).**

$$\left(\operatorname{D5.S3.Analytic.MomentMinors.BoundedKurtosisLimitRefutation.claim}\right) \Leftrightarrow \left(\forall \left(L: \mathbb{R}\right), \left(\forall \left(U: \mathbb{R}\right), \left(\left(L < U\right) \to \left(\forall \left(\mu: \operatorname{MeasureTheory.Measure}\left(\mathbb{R}\right)\right), \left(\left(\operatorname{MeasureTheory.IsProbabilityMeasure}\left(\mu\right)\right) \to \left(\left(\operatorname{Filter.Eventually}\left(\lambda \left(x: \mathbb{R}\right) \mapsto \left(\left(L \le x\right) \land \left(x \le U\right)\right), \operatorname{MeasureTheory.ae}\left(\mu\right)\right)\right) \to \left(\left(\left(0: \mathbb{R}\right) < \operatorname{D5.S3.Analytic.MomentMinors.Defs.mean}\left(\mu\right)\right) \to \left(\left(\left(0: \mathbb{R}\right) < \operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, \left(2: \mathbb{N}\right), \mu\right)\right) \to \left(\operatorname{let} \left(\sigma: \mathbb{R}\right) := \operatorname{Real.sqrt}\left(\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, \left(2: \mathbb{N}\right), \mu\right)\right); \left(\operatorname{let} \left(\delta: \mathbb{R}\right) := \frac{\sigma}{\operatorname{D5.S3.Analytic.MomentMinors.Defs.mean}\left(\mu\right)}; \left(\operatorname{let} \left(\delta{min}: \mathbb{R}\right) := \left|\left(\left(1: \mathbb{R}\right)\right) - \left(\frac{L}{\operatorname{D5.S3.Analytic.MomentMinors.Defs.mean}\left(\mu\right)}\right)\right|; \left(\operatorname{let} \left(\delta{max}: \mathbb{R}\right) := \left|\left(\left(1: \mathbb{R}\right)\right) - \left(\frac{U}{\operatorname{D5.S3.Analytic.MomentMinors.Defs.mean}\left(\mu\right)}\right)\right|; \left(\operatorname{let} \left(\delta_{1}: \mathbb{R}\right) := \operatorname{min}\left(\delta{min}, \delta{max}\right); \left(\operatorname{let} \left(\delta_{2}: \mathbb{R}\right) := \operatorname{max}\left(\delta{min}, \delta{max}\right); \left(\operatorname{let} \left(\delta': \mathbb{R}\right) := \operatorname{Real.sqrt}\left(\left(\delta_{1}\right) \cdot \left(\delta_{2}\right)\right); \left(\operatorname{let} \left(D4: \mathbb{R}\right) := \frac{\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, \left(4: \mathbb{N}\right), \mu\right)}{\left(\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, \left(2: \mathbb{N}\right), \mu\right)\right)^{\left(2: \mathbb{N}\right)}}; \left(\left(\left(\delta < \delta_{1}\right) \to \left(\left(\left(1: \mathbb{R}\right) \le D4\right) \land \left(D4 \le \operatorname{D5.S3.Analytic.MomentMinors.BoundedKurtosisLimitRefutation.kurtosisBound}\left(\delta, \delta_{2}\right)\right)\right)\right) \land \left(\left(\delta_{1} \le \delta\right) \to \left(\left(\delta < \delta'\right) \to \left(\left(\operatorname{D5.S3.Analytic.MomentMinors.BoundedKurtosisLimitRefutation.kurtosisBound}\left(\delta, \delta_{1}\right) \le D4\right) \land \left(D4 \le \operatorname{D5.S3.Analytic.MomentMinors.BoundedKurtosisLimitRefutation.kurtosisBound}\left(\delta, \delta_{2}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David J. Meer; Eric R. Weeks (2024). *Bounded distributions place limits on skewness and larger moments*. DOI: [10.1371/journal.pone.0297862](https://doi.org/10.1371/journal.pone.0297862). URL: <https://arxiv.org/abs/2308.05006v2>.

*Commentary.*

The proposition concerns every real interval with L < U and every probability measure μ concentrated almost everywhere on that interval, with positive mean and positive second central moment. Here mean μ is the integral of x, and centralMoment id k μ is the integral of (x − mean μ)ᵏ. The standard deviation σ is the square root of the second central moment, δ is σ divided by the mean, and D4 is the fourth central moment divided by the square of the second. These are the moment conventions of plos_latex_template.tex, lines 228–236 and 290–293. The quantities δmin and δmax are the absolute normalized distances from the mean to L and U; δ₁ and δ₂ are their minimum and maximum, and δ′ is the square root of their product, as in lines 437–460. When δ < δ₁, the proposition requires D4 to lie between 1 and kurtosisBound δ δ₂. When δ₁ ≤ δ and δ < δ′, it requires D4 to lie between kurtosisBound δ δ₁ and kurtosisBound δ δ₂. These are the two implications in equation D4mostgeneral, lines 461–464, read as bounds for all such probability laws in the sense suggested at line 467. The proposition makes no assertion for δ ≥ δ′.

**Theorem 1.3 (A three-point counterexample).**

$$\neg \left(\operatorname{D5.S3.Analytic.MomentMinors.BoundedKurtosisLimitRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/meer-weeks-2024-bounded-kurtosis-limit-refutation` (refuted) by `D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"meer-weeks-2024-bounded-kurtosis-limit-refutation","declaration_gid":"D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* David J. Meer; Eric R. Weeks (2024). *Bounded distributions place limits on skewness and larger moments*. DOI: [10.1371/journal.pone.0297862](https://doi.org/10.1371/journal.pone.0297862). URL: <https://arxiv.org/abs/2308.05006v2>.

*Commentary.*

Let ν assign masses 1/4, 1/2 and 1/4 to the real points 1, 2 and 3. It is the sum of the corresponding weighted Dirac measures. The masses are nonnegative and sum to one, so ν is a probability measure. Each of the three points belongs to [1,3], giving 1 ≤ x ≤ 3 almost everywhere.

For every function f from the reals to the reals, f is integrable against each of these weighted Dirac measures. Splitting the integral over their sum therefore gives ∫ f dν = f(1)/4 + f(2)/2 + f(3)/4. Taking f(x) = x yields mean ν = 1/4 + 2/2 + 3/4 = 2. Subtracting this mean and taking the second power yields the second central moment 1/4 + 0 + 1/4 = 1/2. Taking the fourth power gives the same value 1/2 for the fourth central moment.

Put s = √(1/2). Since 1/2 < 1, the square-root inequality gives s < 1, hence s/2 < 1/2. Also s² = 1/2 and (1/2)/(s/2) = 2s, while (s/2)/(1/2) = s. Substitution into the two-point expression gives kurtosisBound (s/2) (1/2) = (s − 2s)² + 1 = 3/2.

Suppose claim holds. Apply it with L = 1, U = 3 and μ = ν. The mean and variance are positive, and the interval condition was established above. Substituting the computed moments gives δ = s/2, δmin = |1 − 1/2| = 1/2 and δmax = |1 − 3/2| = 1/2. Thus δ₁ = δ₂ = 1/2 and D4 = (1/2)/(1/2)² = 2. Since δ < δ₁, the upper inequality in the first implication gives 2 ≤ kurtosisBound (s/2) (1/2). The value 3/2 computed above would then give 2 ≤ 3/2, a contradiction.

## References

- Truth anchor: `D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.claim`
- Truth anchor: `D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.kurtosisBound`
- Truth anchor: `D5/S3/Analytic/MomentMinors/BoundedKurtosisLimitRefutation.result`
- Dependency: [D5/S3/Analytic/MomentMinors/Defs](Defs.md)

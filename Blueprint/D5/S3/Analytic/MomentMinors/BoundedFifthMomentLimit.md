# One-sided fifth moment bounds

## Abstract

Fifth central moment inequalities for probability laws bounded on one side.

**Definition 1.1 (The two-point fifth moment expression).**

$$\forall (z: \mathbb{R}), ((\operatorname{D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit.fifthBound}\left(z\right): \mathbb{R}) = ((((z)^{3}) - (z)) + (\operatorname{Inv.inv}\left(z\right))) - ((\operatorname{Inv.inv}\left(z\right))^{3}))$$

*Formalization.* `D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit.fifthBound` (`✓ std3`).

*Citation.* David J. Meer; Eric R. Weeks (2024). *Bounded distributions place limits on skewness and larger moments*. DOI: [10.1371/journal.pone.0297862](https://doi.org/10.1371/journal.pone.0297862). URL: <https://arxiv.org/abs/2308.05006v2>.

*Commentary.*

The function fifthBound is the real expression z³ − z + z⁻¹ − (z⁻¹)³. For positive z it is the standardized fifth moment of the two-point law whose ratio of standard deviation to distance from the lower endpoint to the mean is z. Its definition also assigns a value at zero using the real inverse, for which the inverse of zero is zero. The expression occurs in Meer and Weeks, arXiv:2308.05006v2, plos_latex_template.tex, lines 500–510.

**Definition 1.2 (The two one-sided inequalities).**

$$(\operatorname{D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit.claim}) \Leftrightarrow (\forall (\mu: \operatorname{MeasureTheory.Measure}\left(\mathbb{R}\right)), ((\operatorname{MeasureTheory.IsProbabilityMeasure}\left(\mu\right)) \to ((\operatorname{MeasureTheory.Integrable}\left(\lambda (x: \mathbb{R}) \mapsto ((\left|x\right|)^{5}), \mu\right)) \to (((0: \mathbb{R}) < \operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 2, \mu\right)) \to ((\forall (L: \mathbb{R}), ((\operatorname{Filter.Eventually}\left(\lambda (x: \mathbb{R}) \mapsto (L \le x), \operatorname{MeasureTheory.ae}\left(\mu\right)\right)) \to (\operatorname{D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit.fifthBound}\left(\frac{\operatorname{Real.sqrt}\left(\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 2, \mu\right)\right)}{(\operatorname{D5.S3.Analytic.MomentMinors.Defs.mean}\left(\mu\right)) - (L)}\right) \le \frac{\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 5, \mu\right)}{(\operatorname{Real.sqrt}\left(\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 2, \mu\right)\right))^{5}}))) \land (\forall (U: \mathbb{R}), ((\operatorname{Filter.Eventually}\left(\lambda (x: \mathbb{R}) \mapsto (x \le U), \operatorname{MeasureTheory.ae}\left(\mu\right)\right)) \to (\frac{\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 5, \mu\right)}{(\operatorname{Real.sqrt}\left(\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 2, \mu\right)\right))^{5}} \le -(\operatorname{D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit.fifthBound}\left(\frac{\operatorname{Real.sqrt}\left(\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 2, \mu\right)\right)}{(U) - (\operatorname{D5.S3.Analytic.MomentMinors.Defs.mean}\left(\mu\right))}\right))))))))))$$

*Formalization.* `D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* David J. Meer; Eric R. Weeks (2024). *Bounded distributions place limits on skewness and larger moments*. DOI: [10.1371/journal.pone.0297862](https://doi.org/10.1371/journal.pone.0297862). URL: <https://arxiv.org/abs/2308.05006v2>.

*Commentary.*

The proposition concerns every Borel probability measure μ on the real line with integrable fifth absolute moment and strictly positive variance. For every almost sure lower bound L, the standardized fifth central moment is at least fifthBound at the ratio of standard deviation to mean μ − L. For every almost sure upper bound U, it is at most the negative of fifthBound at the ratio of standard deviation to U − mean μ. Here mean μ is the integral of x, and centralMoment id k μ is the integral of (x − mean μ)ᵏ. These moments follow the conventions in plos_latex_template.tex, lines 228–236; the ratios are those of lines 397–408, and the fifth moment question is in lines 506–510. The lower and upper bounds are separate implications, so either can be used without assuming a bound on the other side.

**Theorem 1.3 (Fifth central moment bounds).**

$$\forall (\mu: \operatorname{MeasureTheory.Measure}\left(\mathbb{R}\right)), ((\operatorname{MeasureTheory.IsProbabilityMeasure}\left(\mu\right)) \to ((\operatorname{MeasureTheory.Integrable}\left(\lambda (x: \mathbb{R}) \mapsto ((\left|x\right|)^{5}), \mu\right)) \to (((0: \mathbb{R}) < \operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 2, \mu\right)) \to ((\forall (L: \mathbb{R}), ((\operatorname{Filter.Eventually}\left(\lambda (x: \mathbb{R}) \mapsto (L \le x), \operatorname{MeasureTheory.ae}\left(\mu\right)\right)) \to (\operatorname{D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit.fifthBound}\left(\frac{\operatorname{Real.sqrt}\left(\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 2, \mu\right)\right)}{(\operatorname{D5.S3.Analytic.MomentMinors.Defs.mean}\left(\mu\right)) - (L)}\right) \le \frac{\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 5, \mu\right)}{(\operatorname{Real.sqrt}\left(\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 2, \mu\right)\right))^{5}}))) \land (\forall (U: \mathbb{R}), ((\operatorname{Filter.Eventually}\left(\lambda (x: \mathbb{R}) \mapsto (x \le U), \operatorname{MeasureTheory.ae}\left(\mu\right)\right)) \to (\frac{\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 5, \mu\right)}{(\operatorname{Real.sqrt}\left(\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 2, \mu\right)\right))^{5}} \le -(\operatorname{D5.S3.Analytic.MomentMinors.BoundedFifthMomentLimit.fifthBound}\left(\frac{\operatorname{Real.sqrt}\left(\operatorname{ProbabilityTheory.centralMoment}\left(\operatorname{id}, 2, \mu\right)\right)}{(U) - (\operatorname{D5.S3.Analytic.MomentMinors.Defs.mean}\left(\mu\right))}\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit.result` (`✓ std3`). ∎

*Resolves.* `Problems/meer-weeks-2024-bounded-fifth-moment-limit` (proved) by `D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"meer-weeks-2024-bounded-fifth-moment-limit","declaration_gid":"D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* David J. Meer; Eric R. Weeks (2024). *Bounded distributions place limits on skewness and larger moments*. DOI: [10.1371/journal.pone.0297862](https://doi.org/10.1371/journal.pone.0297862). URL: <https://arxiv.org/abs/2308.05006v2>.

*Commentary.*

First, integrability of |x|⁵ places the identity function in L⁵. Subtracting a real constant c and decreasing the exponent on a probability space shows that (x − c)ᵏ is integrable for every natural k ≤ 5. In particular the first, second and fifth centered powers are integrable.

Suppose L ≤ x almost everywhere. The nonnegative integrable function x − L has integral mean μ − L. If this integral were zero, then x − L would vanish almost everywhere, the mean would equal L, and the second central moment would be zero. Positive variance therefore gives a = mean μ − L > 0.

For real a, b and y with y ≥ −a, the quadratic Q(y) = y² + (2b − a)y + 3b² − 2ab + a² is nonnegative: it equals (y + b − a/2)² + 2(b − a/4)² + 5a²/8. Consequently R(y) = (y + a)(y − b)²Q(y) is nonnegative. Expanding gives y⁵ − R(y) = Ay² + By + C, where A = −a³ + 2a²b − 3ab² + 4b³, B = 2a³b − 4a²b² + 6ab³ − 3b⁴, and C = −a³b² + 2a²b³ − 3ab⁴. Thus Ay² + By + C ≤ y⁵.

Set a = mean μ − L, b = centralMoment id 2 μ / a, and y = x − mean μ. The centered first moment is zero and the centered second moment is ab. The support assumption gives y ≥ −a almost everywhere. Integrating the polynomial inequality is justified by the centered-power integrability above and gives Aab + B·0 + C ≤ centralMoment id 5 μ. The left side simplifies to ab(b − a)(a² + b²).

To divide by the standard deviation, put v = centralMoment id 2 μ, M = centralMoment id 5 μ and s = √v. Since v > 0, we have s > 0 and s² = v. Expansion after clearing the nonzero denominators a and s gives fifthBound(s/a)s⁵ = a(v/a)(v/a − a)(a² + (v/a)²). The integrated inequality and s⁵ > 0 now give fifthBound(s/a) ≤ M/s⁵. Together with a > 0 this proves the lower-support implication.

For the upper-support implication, let ν be the image of μ under x ↦ −x. Reflection preserves the fifth absolute moment's integrability and gives mean ν = −mean μ. Changing variables in each centered moment gives centralMoment id k ν = (−1)ᵏ centralMoment id k μ. In particular the second central moment is unchanged and the fifth is negated. If x ≤ U almost everywhere for μ, then −U ≤ x almost everywhere for ν. Applying the lower inequality to ν at −U and using mean ν − (−U) = U − mean μ yields the upper inequality for μ. The two implications give the stated conjunction.

## References

- Truth anchor: `D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit.claim`
- Truth anchor: `D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit.fifthBound`
- Truth anchor: `D5/S3/Analytic/MomentMinors/BoundedFifthMomentLimit.result`
- Dependency: [D5/S3/Analytic/MomentMinors/Defs](Defs.md)

# The sharp lower bound on unicyclic skewness plus kurtosis

## Abstract

The sum of skewness and kurtosis of every finite positive unidirectional cycle exceeds −8/27, the greatest lower bound over all cycle sizes.

**Definition 1.1 (The asymptotic lower endpoint).**

$$(\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.lowerBound}: \mathbb{R}) = \frac{-(8: \mathbb{R})}{(27: \mathbb{R})}$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound.lowerBound` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

The real constant −8/27 is the lower endpoint for the sum of skewness and kurtosis in main.tex lines 434-437. Line 424 describes the limit of infinitely many states with one rate a = A/N relative to the other rates; this endpoint corresponds to A = 1/2. The constant will be approached by positive cycles of increasing size.

**Definition 1.2 (Strict finite-cycle inequality and greatest lower bound).**

$$(\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.claim}) \Leftrightarrow ((\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \to (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.lowerBound} < (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) + (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right))))))) \land (\operatorname{IsGLB}\left(\{(s: \mathbb{R}) \mid \exists (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \land (\exists (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \land (s = (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) + (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right))))))\}, \operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.lowerBound}\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

For every natural n at least two and every strictly positive real rate vector k indexed by Fin n, skewness k + kurtosis k strictly exceeds lowerBound. The same constant is the greatest lower bound of all these values as n varies. The source states in main.tex lines 434-437: “min(S + K) = −8/27 for A = 1/2, max(S + K) = 2 for A → 0.” Line 424 specifies the asymptotic limit. The assertion here reads the lower minimum as an infimum and adds strictness for every finite positive cycle. The source calls the extremal-topology assertion a numerical conjecture in line 792. Only the lower endpoint for the two inverse-rate expressions on unidirectional cycles is asserted here; neither a finite-size extremal topology nor the upper endpoint is asserted.

**Theorem 1.3 (The strict bound and its sharp limiting value).**

$$(\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \to (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.lowerBound} < (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) + (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right))))))) \land (\operatorname{IsGLB}\left(\{(s: \mathbb{R}) \mid \exists (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \land (\exists (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \land (s = (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) + (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right))))))\}, \operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.lowerBound}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

Write Rⱼ = ∑ᵢ(kᵢ)⁻ʲ and xᵢ = (kᵢ)⁻¹/R₁, and put p = ∑ᵢxᵢ², q = ∑ᵢxᵢ³ and r = ∑ᵢxᵢ⁴. The normalized kurtosis identity, together with the inverse-rate formula for skewness, gives S + K = 18p² − 22q + 6r/p by factoring the powers of R₁ out of the sums. For n ≥ 2 and positive k, R₁ > 0: each summand is positive, including the one at i = 0. Thus x is positive. The moment inequalities give p > 0, q ≥ 0, q² ≤ pr and r < p². Here q² ≤ pr is Cauchy-Schwarz applied to x and its coordinatewise square, and r < p² follows from the strict square-sum inequality for the at least two positive coordinates xᵢ².

Set t = q/p, e = r/p − t² and d = p − t². Then t ≥ 0, q = pt and e ≥ 0 by q² ≤ pr. Since q² ≤ pr < p³, one has t² < p and d > 0. Also r = p(t² + e), so S + K + 8/27 = 18p² − 22pt + 6t² + 6e + 8/27. If t ≤ 11/18, this equals 6e + 18(p − (11/18)t)² + (13/18)((11/18)² − t²) + 155/5832. All terms except the positive last constant are nonnegative, since 0 ≤ t ≤ 11/18. Hence the sum is strictly positive.

If t > 11/18, substitute d = p − t² to obtain instead 6e + d(18d + 36t² − 22t) + (t − 2/3)²(18t² + 2t + 2/3). The factor 36t² − 22t = 2t(18t − 11) is nonnegative, so 18d + 36t² − 22t > 0. Its product with d is strictly positive. The polynomial 18t² + 2t + 2/3 is positive, as is seen by completing its square, so the remaining square term is nonnegative. Together with e ≥ 0 this proves positivity in the second case. The normalized expression therefore gives S + K > −8/27 for every finite positive cycle with at least two states.

For sharpness, let m ≥ 1 be natural and take m + 1 rates with k₀ = (2(m : ℝ))⁻¹ and kᵢ = 1 for i ≠ 0. These rates are positive. For each natural j their inverse-rate power sum is Rⱼ = (2(m : ℝ))ʲ + (m : ℝ). Substitution in the skewness and kurtosis formulas and cancellation gives S + K + 8/27 = 2(60(m : ℝ)² − 8(m : ℝ) + 1) /[27(m : ℝ)²(4(m : ℝ) + 1)]. Define F(t) = 2(60t − 8t² + t³)/[27(4 + t)]. The preceding value equals F(1/(m : ℝ)). This rational function is continuous at zero and F(0) = 0. Using m + 1 in place of m, the reciprocals 1/((m + 1 : ℕ) : ℝ) tend to zero, so the sums for these positive cycles of size m + 2 tend to lowerBound.

Finally, the strict inequality makes lowerBound a lower bound of the set of all positive-cycle sums. Any other lower bound b is no greater than every sum in the explicit sequence of cycles of size m + 2. Passing to the limit gives b ≤ lowerBound. Thus lowerBound is the greatest lower bound, and no finite positive cycle attains it.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound.lowerBound`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound.result`
- Dependency: [D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound](UnicyclicKurtosisLowerBound.md)
- Dependency: [D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum](UnicyclicSkewnessMinimum.md)

# The sharp lower bound on unicyclic current kurtosis

## Abstract

The kurtosis of every finite positive unidirectional cycle exceeds −(1 + √5)/10, and this constant is the greatest lower bound over all cycle sizes.

**Definition 1.1 (Kurtosis from inverse-rate power sums).**

$$\forall (n: \mathbb{N}), (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right): \mathbb{R}) = ((\frac{((15: \mathbb{R})) \cdot ((\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (2: \mathbb{N}), \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(i\right)\right))\right))^{(2: \mathbb{N})})}{(\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (1: \mathbb{N}), \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(i\right)\right))\right))^{(4: \mathbb{N})}}) - (\frac{((20: \mathbb{R})) \cdot (\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (3: \mathbb{N}), \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(i\right)\right))\right))}{(\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (1: \mathbb{N}), \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(i\right)\right))\right))^{(3: \mathbb{N})}})) + (\frac{((6: \mathbb{R})) \cdot (\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (4: \mathbb{N}), \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(i\right)\right))\right))}{((\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (1: \mathbb{N}), \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(i\right)\right))\right))^{(2: \mathbb{N})}) \cdot (\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (2: \mathbb{N}), \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(i\right)\right))\right))})))$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.kurtosis` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

For a real rate vector k indexed by Fin n, powerSum n j sums the jth powers of its argument over Fin n. The source defines kurtosis as the fourth scaled current cumulant divided by the second in main.tex line 54. Substituting the current cumulants in lines 773-775 and the waiting-time cumulants in lines 787-790 gives the displayed rational expression. This definition uses total real inversion and division, so it is defined for every natural n and every real rate vector. Its interpretation as a current cumulant ratio concerns positive rates on a unidirectional cycle with at least two states; the expression itself does not construct a stochastic process.

**Definition 1.2 (The asymptotic lower endpoint).**

$$(\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.lowerBound}: \mathbb{R}) = \frac{-(((1: \mathbb{R})) + (\operatorname{Real.sqrt}\left((5: \mathbb{R})\right)))}{(10: \mathbb{R})}$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.lowerBound` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

The constant is the lower endpoint for kurtosis stated in main.tex line 132. Section III E 1, lines 424-427, gives this value in the limit of infinitely many states, with one rate equal to A/n and all other rates equal to one, where A = (3 - √5)/2. It is an infimum over cycle sizes, rather than a value attained by a finite positive cycle with at least two states.

**Definition 1.3 (Strict finite-cycle inequality and greatest lower bound).**

$$(\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.claim}) \Leftrightarrow ((\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \to (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.lowerBound} < \operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right)))))) \land (\operatorname{IsGLB}\left(\{(s: \mathbb{R}) \mid \exists (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \land (\exists (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \land (s = \operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right)))))\}, \operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.lowerBound}\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

For every natural n at least two and every strictly positive vector k indexed by Fin n, kurtosis k strictly exceeds lowerBound. The same lowerBound is the greatest lower bound of the set of all such values, allowing n to vary. This is the unidirectional lower-bound assertion of main.tex lines 417 and 424-427, with the asymptotic minimum read as an infimum and with strictness for each finite cycle. The source's choice of extremal rates is a numerical conjecture in line 417 and in the Appendix, line 792. The assertion here concerns only the lower endpoint for the displayed inverse-rate expression on positive unidirectional cycles.

**Theorem 1.4 (Kurtosis in rescaled inverse rates).**

$$\forall (n: \mathbb{N}), (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right) = ((((15: \mathbb{R})) \cdot ((\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (2: \mathbb{N}), \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\frac{\operatorname{Inv.inv}\left(k\left(i\right)\right)}{\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (1: \mathbb{N}), \lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(j\right)\right))\right)})\right))^{(2: \mathbb{N})})) - (((20: \mathbb{R})) \cdot (\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (3: \mathbb{N}), \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\frac{\operatorname{Inv.inv}\left(k\left(i\right)\right)}{\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (1: \mathbb{N}), \lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(j\right)\right))\right)})\right)))) + (\frac{((6: \mathbb{R})) \cdot (\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (4: \mathbb{N}), \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\frac{\operatorname{Inv.inv}\left(k\left(i\right)\right)}{\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (1: \mathbb{N}), \lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(j\right)\right))\right)})\right))}{\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (2: \mathbb{N}), \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\frac{\operatorname{Inv.inv}\left(k\left(i\right)\right)}{\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (1: \mathbb{N}), \lambda (j: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(j\right)\right))\right)})\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

Dividing every inverse rate by its first power sum rewrites kurtosis as 15 times the square of the second power sum, minus 20 times the third, plus 6 times the fourth divided by the second. The identity holds for every natural n and every real vector k, using total real inversion and division. To prove it, factor the normalization denominator out of each sum. If the first or second inverse-rate power sum is zero, simplify using division by zero; otherwise clear the nonzero denominators.

**Theorem 1.5 (Four inequalities for positive-coordinate power sums).**

$$\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (x: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < x\left(i\right))) \to (((0: \mathbb{R}) < \operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (2: \mathbb{N}), x\right)) \land (((0: \mathbb{R}) \le \operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (3: \mathbb{N}), x\right)) \land (((\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (3: \mathbb{N}), x\right))^{(2: \mathbb{N})} \le (\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (2: \mathbb{N}), x\right)) \cdot (\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (4: \mathbb{N}), x\right))) \land (\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (4: \mathbb{N}), x\right) < (\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, (2: \mathbb{N}), x\right))^{(2: \mathbb{N})})))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

For a strictly positive real vector x on Fin n with n at least two, the second power sum is positive and the third is nonnegative. Cauchy-Schwarz applied to x and its coordinatewise square bounds the square of the third power sum by the product of the second and fourth. The strict square-sum inequality applied to the positive coordinates xᵢ² bounds the fourth power sum strictly below the square of the second.

**Theorem 1.6 (The strict bound and its sharp limiting value).**

$$(\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \to (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.lowerBound} < \operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right)))))) \land (\operatorname{IsGLB}\left(\{(s: \mathbb{R}) \mid \exists (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \land (\exists (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \land (s = \operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right)))))\}, \operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.lowerBound}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/ptaszynski-2022-unidirectional-kurtosis-lower-bound` (proved) by `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ptaszynski-2022-unidirectional-kurtosis-lower-bound","declaration_gid":"D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

First write Rⱼ = ∑ᵢ(kᵢ)⁻ʲ and normalize the inverse rates by xᵢ = (kᵢ)⁻¹/R₁. Factoring R₁ out of each power sum gives kurtosis k = 15a² - 20b + 6c/a, where a = ∑ᵢxᵢ², b = ∑ᵢxᵢ³ and c = ∑ᵢxᵢ⁴. The algebraic identity holds with total division even when R₁ or R₂ vanishes: those cases are handled separately before clearing denominators.

For a positive vector x on Fin n with n ≥ 2, the squares are nonnegative and the square at i = 0 is positive, so Finset.sum_pos' gives a > 0. Positivity of the cubes gives b ≥ 0. Cauchy-Schwarz, in the form Finset.sum_mul_sq_le_sq_mul_sq, applied to x and its coordinatewise square gives b² ≤ ac. HermiteMomentBounds.sum_sq_lt_sq_sum applied to the positive coordinates yₗ = xₗ² gives ∑ₗyₗ² < (∑ₗyₗ)². The power identity (xₗ²)² = xₗ⁴ then gives c < a².

Put C = lowerBound and f(u) = 15u⁴ - 20u³ + 6u². For u ≥ 0, direct expansion using (√5)² = 5 gives f(u) - C = (u - (5 + √5)/10)² [15u² + (3√5 - 5)u + (√5 - 1)/2]. The comparisons 5/3 ≤ √5 and 1 ≤ √5 show that the coefficients 3√5 - 5 and (√5 - 1)/2 are nonnegative, so every factor on the right is nonnegative and f(u) ≥ C.

Now suppose a > 0, b ≥ 0, b² ≤ ac and c < a², and set t = b/a. Then t ≥ 0, at = b, t² < a and at² ≤ c. Consequently 15a² - 20b + 6c/a ≥ Q, where Q = 15a² - 20at + 6t². If t ≤ 2/3, then t² ≤ 4/9 and Q = (5/3)(3a - 2t)² - (2/3)t² ≥ -8/27. The relation (√5)² = 5 and √5 ≥ 0 gives C < -8/27, so Q > C. If t > 2/3, then 15(a + t²) - 20t > 0, since a > t² and t(3t - 2) > 0. Thus Q - f(t) = (a - t²)[15(a + t²) - 20t] > 0. Combining this with f(t) ≥ C again gives Q > C.

For positive rates k, Finset.sum_pos' gives R₁ > 0 from the nonnegative inverse rates and the positive inverse rate at i = 0. The rescaled vector x is therefore positive. Applying its moment inequalities and the preceding estimate to the rescaled kurtosis identity proves lowerBound < kurtosis k for every n ≥ 2.

To approach the bound, put A = (3 - √5)/2 and, for each natural m, take n = m + 2, k₀ = A/((m + 2 : ℕ) : ℝ) and kᵢ = 1 for i ≠ 0. Since √5 < 3, A > 0 and every rate is positive. For each natural j, their inverse-rate power sum is Rⱼ = (((m : ℝ) + 2)/A)ʲ + ((m : ℝ) + 1). Introduce the rational function F(a,t) = 15(1 + a²(t - t²))²/(1 + a - at)⁴ - 20(1 + a³(t² - t³))/(1 + a - at)³ + 6(1 + a⁴(t³ - t⁴))/[(1 + a - at)²(1 + a²(t - t²))]. Substitution of the power sums and clearing positive denominators gives kurtosis k = F(A,1/((m + 2 : ℕ) : ℝ)). Indeed 0 < 1/((m + 2 : ℕ) : ℝ) ≤ 1, so both 1 + A - A/((m + 2 : ℕ) : ℝ) and 1 + A²(1/((m + 2 : ℕ) : ℝ) - (1/((m + 2 : ℕ) : ℝ))²) are positive.

The function F(A,t) is continuous at t = 0, since its denominators there are powers of 1 + A > 0 and the factor 1. As m tends to infinity, 1/((m + 2 : ℕ) : ℝ) tends to zero. Expanding F(A,0), substituting A = (3 - √5)/2 and reducing the powers (√5)² = 5, (√5)³ = 5√5, (√5)⁴ = 25 and (√5)⁵ = 25√5 gives F(A,0) = C. Hence the kurtosis values of these positive cycles tend to C.

Finally, the strict inequality implies that C is a lower bound of the set of positive-cycle kurtosis values. If b is any other lower bound, it is at most each value in the explicit sequence. Passing to its limit gives b ≤ C. Thus C is the greatest lower bound, and the strict finite-cycle inequality shows that no finite positive cycle attains it.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.kurtosis`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.lowerBound`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.moments`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.normalized`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.result`
- Dependency: [D5/S3/Analytic/Interpolation/HermiteMomentBounds](../Analytic/Interpolation/HermiteMomentBounds.md)
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/Foundations](../Quantum/Transport/StrongAbsorption/Foundations.md)

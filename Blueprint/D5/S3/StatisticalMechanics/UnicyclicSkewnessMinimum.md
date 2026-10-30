# The minimum skewness of a unidirectional cycle

## Abstract

For every unidirectional cycle with at least two states, the least skewness of positive rates is attained when one rate is the reciprocal of the number of other rates.

**Definition 1.1 (Skewness from inverse-rate power sums).**

$$\forall (n: \mathbb{N}), (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right): \mathbb{R}) = (\frac{(3) \cdot ((\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, 2, \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(i\right)\right))\right))^{2})}{(\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, 1, \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(i\right)\right))\right))^{4}}) - (\frac{(2) \cdot (\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, 3, \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(i\right)\right))\right))}{(\operatorname{D5.S3.Quantum.Transport.StrongAbsorption.Foundations.powerSum}\left(n, 1, \lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Inv.inv}\left(k\left(i\right)\right))\right))^{3}})))$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.skewness` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

For n real rates k, powerSum n j sums the jth powers of its argument over Fin n. The displayed expression is the third scaled current cumulant divided by the first. The source defines this ratio in main.tex line 53; its Appendix gives the current and waiting-time cumulants in lines 772-789. Substituting those formulas gives the expression in inverse-rate power sums. The definition is a total real-valued function for every natural n and every real rate vector; the current interpretation and the minimum below concern positive rates on cycles with n at least two.

**Definition 1.2 (The finite-state minimum value).**

$$\forall (n: \mathbb{N}), ((\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.minimumValue}\left(n\right): \mathbb{R}) = \frac{-(((8) - ((8) \cdot ((\operatorname{Nat.cast}\left(n\right): \mathbb{R})))) + (((\operatorname{Nat.cast}\left(n\right): \mathbb{R}))^{2}))}{(16) \cdot ((((\operatorname{Nat.cast}\left(n\right): \mathbb{R})) - (1))^{2})})$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.minimumValue` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

This is the value in Section III E 1, main.tex line 420. The argument n is a natural number, and each occurrence of n in the rational expression is explicitly cast to the reals. The expression is defined for every n using real division; its asserted role as a minimum is restricted to n at least two.

**Definition 1.3 (An attained minimum over all positive rate vectors).**

$$(\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\operatorname{IsLeast}\left(\{(s: \mathbb{R}) \mid \exists (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \land (s = \operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)))\}, \operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.minimumValue}\left(n\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

For every natural n at least two, minimumValue n belongs to the set of skewness values of positive vectors k indexed by Fin n and is no larger than any member of that set. Thus IsLeast includes both attainment and the universal lower bound. This expresses the skewness-minimum part of the extremal-topology conjecture in Section III E 1, main.tex lines 416-420, and the Appendix, line 792.

**Theorem 1.4 (The sharp lower bound and its attaining rates).**

$$\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/ptaszynski-2022-unicyclic-skewness-minimum` (proved) by `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ptaszynski-2022-unicyclic-skewness-minimum","declaration_gid":"D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

First normalize inverse rates. For n positive and k positive, let R be the sum of the inverse rates and set xᵢ = (kᵢ)⁻¹/R. Every inverse rate is positive, so this vector is nonnegative, nonzero before normalization, and has sum one. Dividing its power sums by the corresponding powers of R shows that the skewness equals F(x) = 3p² - 2q, where p = ∑ᵢ xᵢ² and q = ∑ᵢ xᵢ³.

The algebraic estimate uses real numbers r, a, b, p, q with r ≥ 1, a + rb = 1, b ≤ a, a ≥ 0, p ≥ a² + rb², and q ≤ (a + 2b)p - 2ab - b² + (r + 1)ab². Set d = p - (a² + rb²), h = 3(a² + rb²)² - 2(a³ + rb³), and g = -(r² - 6r + 1)/(16r²). Then d ≥ 0, r > 0, b = (1 - a)/r, and z = (r + 1)a - 1 ≥ 0. Direct expansion gives h - g = (2a - 1)²[12z² + 4(r - 1)z + (r - 1)²]/(16r²), so h ≥ g. The upper bound for q also gives 3p² - 2q ≥ h + 3d² + 2(a - b)(3a - 1)d.

If 3a - 1 ≥ 0, every correction on the right is nonnegative, giving 3p² - 2q ≥ g. If 3a - 1 < 0, the relations a + rb = 1 and b ≤ a imply r ≥ 2. Define u = 18(r + 1)a² + 3(r² - 2r - 12)a + r² - 8r + 18. For 2 ≤ r ≤ 8, the identity 72(r + 1)u = [36(r + 1)a + 3(r² - 2r - 12)]² + 9r(8 - r)(r - 2)² proves u ≥ 0. For r > 8, all three terms in the defining expression for u are nonnegative, again giving u ≥ 0.

In this second case, another expansion gives h - (a - b)²(3a - 1)²/3 - g = (1/3 - a)u/(9r²) + [11(r - 2)² + 10(r - 2) + 3]/(432r²), which is nonnegative. Completing the remaining square yields h + 3d² + 2(a - b)(3a - 1)d - g = [h - (a - b)²(3a - 1)²/3 - g] + [3d + (a - b)(3a - 1)]²/3 ≥ 0. This proves the algebraic estimate in both cases.

Now let x be any point of the closed standard simplex on Fin n, with n ≥ 2. Choose i with maximal coordinate and put a = xᵢ, r = (n : ℝ) - 1, b = (1 - a)/r, p = ∑ⱼ xⱼ², q = ∑ⱼ xⱼ³. Then r ≥ 1 and a + rb = 1. Nonnegativity gives a ≥ 0, and summing xⱼ ≤ a gives 1 ≤ (n : ℝ)a, hence b ≤ a. Expanding ∑ⱼ(xⱼ - b)² = p - 2b + (n : ℝ)b² and retaining its ith term gives p ≥ a² + rb². Moreover each (a - xⱼ)(xⱼ - b)² is nonnegative. Their sum is -q + (a + 2b)p - (2ab + b²) + (n : ℝ)ab², which gives the required upper bound for q. Applying the algebraic estimate and substituting r = (n : ℝ) - 1 proves F(x) ≥ minimumValue n.

For attainment, write n = m + 1, so m > 0, and take k₀ = (m : ℝ)⁻¹ and kᵢ = 1 for i ≠ 0. These rates are positive. For each natural j, the jth power sum of their inverse rates is (m : ℝ)ʲ + (m : ℝ). Substituting the first three such sums into the skewness formula and clearing the positive denominators gives skewness k = minimumValue n. Thus the rate vector is (1/(n - 1), 1, …, 1), and its normalized inverse rates are (1/2, 1/(2(n - 1)), …, 1/(2(n - 1))).

Finally fix n ≥ 2. The explicit rates put minimumValue n in the set of positive-rate skewness values. For any member s, choose its positive rate vector k, replace its skewness by F of the normalized inverse rates, and apply the closed-simplex lower bound. Hence minimumValue n ≤ s, which proves IsLeast. The conclusion concerns the finite-n skewness minimum for positive rates on unidirectional cycles.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.minimumValue`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.result`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.skewness`
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/CollatzWielandt](../Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/CollatzWielandt.md)
- Dependency: [D5/S3/Quantum/Transport/StrongAbsorption/Foundations](../Quantum/Transport/StrongAbsorption/Foundations.md)

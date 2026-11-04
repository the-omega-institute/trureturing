# The exact upper endpoint of unicyclic skewness minus kurtosis

## Abstract

For every finite cycle size at least two and every positive real rate vector, S − K is at most B = 3(107 + 51√17)/2048; B is the least upper bound of all these actual values.

**Definition 1.1 (The source's upper endpoint).**

$$(\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisUpperBound.upperBound}: \mathbb{R}) = \frac{((3: \mathbb{R})) \cdot (((107: \mathbb{R})) + (((51: \mathbb{R})) \cdot (\operatorname{Real.sqrt}\left((17: \mathbb{R})\right))))}{(2048: \mathbb{R})}$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.upperBound` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

The primary v4 main.tex display at line 432 and Figure 6 concern S − K and give B = 3(107 + 51√17)/2048 at A = (5 − √17)/4. The summary at line 133 instead prints K − S with the same rounded interval. That sign discrepancy is preserved: this result follows the detailed S − K display and Figure 6. Line 424 derives the displayed endpoint analytically on the asymptotic family a = A/N, while line 792 calls the proposed universal extremal topology numerical/conjectural.

**Definition 1.2 (All rates and the realized least upper bound).**

$$(\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisUpperBound.claim}) \Leftrightarrow ((\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \to ((\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) - (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right)) \le \operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisUpperBound.upperBound}))))) \land (\operatorname{IsLUB}\left(\{(s: \mathbb{R}) \mid \exists (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \land (\exists (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \land (s = (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) - (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right))))))\}, \operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisUpperBound.upperBound}\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

The first clause quantifies over every natural n ≥ 2 and every k : Fin n → ℝ with all coordinates strictly positive. Repeated rates retain their multiplicity. Both skewness and kurtosis use this same k. The second clause is IsLUB for exactly the values from those actual rate vectors, with no bound on n. It does not replace realizable vectors by abstract moment triples. No extremal-topology assumption, rational-rate restriction or finite dimension cutoff is imposed.

**Theorem 1.3 (The common normalized difference).**

$$\forall (n: \mathbb{N}), (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) - (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right)) = (((-(12: \mathbb{R})) \cdot ((\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.p}\left(k\right))^{(2: \mathbb{N})})) + (((18: \mathbb{R})) \cdot (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.q}\left(k\right)))) - (\frac{((6: \mathbb{R})) \cdot (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.r}\left(k\right))}{\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound.p}\left(k\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.normalized_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

For every finite real rate vector, S − K equals −12p² + 18q − 6r/p, where p, q and r are the second, third and fourth power sums of the same normalized inverse-rate vector. The identity uses total real division; positivity is required by the extremal bounds, not by this identity.

**Theorem 1.4 (The universal upper bound and sharpness).**

$$(\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \to ((\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) - (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right)) \le \operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisUpperBound.upperBound}))))) \land (\operatorname{IsLUB}\left(\{(s: \mathbb{R}) \mid \exists (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \land (\exists (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \land (s = (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) - (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right))))))\}, \operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisUpperBound.upperBound}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/ptaszynski-2022-unidirectional-skewness-minus-kurtosis-upper-bound` (proved) by `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ptaszynski-2022-unidirectional-skewness-minus-kurtosis-upper-bound","declaration_gid":"D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

The reused definitions are S(k) = 3R₂²/R₁⁴ − 2R₃/R₁³ and K(k) = 15R₂²/R₁⁴ − 20R₃/R₁³ + 6R₄/(R₁²R₂), where Rⱼ = ∑ᵢ kᵢ⁻ʲ. These are ratios of scaled current cumulants, not standardized central moments. Their original normalization identities and normalized_moments give, on xᵢ = kᵢ⁻¹/R₁, the joint facts a = ∑xᵢ² > 0, b = ∑xᵢ³ ≥ 0, b² ≤ ac and c = ∑xᵢ⁴ < a². The common-vector expression is S − K = −12a² + 18b − 6c/a.

Put t = b/a. Then t ≥ 0, t² < a and c/a ≥ t², so S − K ≤ −12a² + 18at − 6t². For t ≤ 3/4, completing the square gives −12(a − 3t/4)² + 3t²/4 ≤ 27/64 ≤ B. For t > 3/4, the difference between f(t) = −12t⁴ + 18t³ − 6t² and that expression is (a − t²)[12(a + t²) − 18t] ≥ 0. The factorization B − f(t) = (t − (9 + √17)/16)² [12t² + ((3√17 − 9)/2)t + (9√17 − 15)/32] is nonnegative for t ≥ 0. This proves the bound on every admissible vector.

For sharpness set u = (9 + √17)/16, so 0 < u < 1. For each natural m, choose n = m + 2 and the actual positive rates k₀ = 1/u and kᵢ = (m + 1)/(1 − u) for i ≠ 0. Their inverse rates sum to one: x₀ = u and the m + 1 remaining coordinates equal (1 − u)/(m + 1). For j = 2,3,4 the power sum is uʲ + (1 − u)ʲ/(m + 1)ʲ⁻¹. With z = 1/(m + 1), substitution gives −12[u² + (1 − u)²z]² + 18[u³ + (1 − u)³z²] − 6[u⁴ + (1 − u)⁴z³]/[u² + (1 − u)²z]. Its denominator at zero is u² > 0; continuity and z → 0 give the limit f(u) = B. Every term belongs to the exact set in claim. Any upper bound of that set bounds this sequence, and passing to the limit makes it at least B. Hence B is IsLUB.

The finite parametrization just used differs from the source's a = A/N. Dividing our rates by their common tail rate gives exceptional rate a = (1 − u)/(u(N − 1)) = A/(N − 1), with A = (1 − u)/u = (5 − √17)/4. Its ratio to A/N is N/(N − 1), which tends to one. The proof evaluates our finite vectors directly; it uses neither an identification of the two finite families nor an unproved classification of extremal topologies.

For n = 2 the physical interpretation uses two successive oriented phase stages and counts one marked winding crossing. The Lean result proves the inverse-rate formulas on positive vectors; it constructs no stochastic process and asserts no renewal theorem or empirical realization. There is no physical n = 1 claim. Bidirectional and multicyclic networks, finite-time cumulants, and standardized moments are outside this statement. Published no-hit claims are restricted to the independently inspected scopes; the unread journal body, unchecked citation-list memberships and global theorem-equivalence search remain limitations.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.normalized_difference`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.result`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.upperBound`
- Dependency: [D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound](UnicyclicSkewnessPlusKurtosisLowerBound.md)

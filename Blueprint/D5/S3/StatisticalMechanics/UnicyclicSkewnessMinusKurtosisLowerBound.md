# The exact lower endpoint of unicyclic skewness minus kurtosis

## Abstract

For every finite cycle size at least two and every strictly positive real rate vector, S − K is at least C = 3(107 − 51√17)/2048; C is the greatest lower bound of all actual values.

**Definition 1.1 (The detailed source's lower endpoint).**

$$(\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisLowerBound.lowerBound}: \mathbb{R}) = \frac{((3: \mathbb{R})) \cdot (((107: \mathbb{R})) - (((51: \mathbb{R})) \cdot (\operatorname{Real.sqrt}\left((17: \mathbb{R})\right))))}{(2048: \mathbb{R})}$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound.lowerBound` (`✓ std3`).

*Citation.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

The primary arXiv v4 main.tex display at line 431 and Figure 6 concern S − K. The summary at line 133 instead labels the interval K − S. This sign conflict is retained: the present endpoint follows the detailed display and figure. Line 424 evaluates the asymptotic exceptional-rate family a = A/N with A = (5 + √17)/4. Line 417 and Appendix line 792 describe the universal extremal topology as numerical/conjectural; no such topology is a hypothesis.

**Definition 1.2 (Every positive vector and the entire actual value set).**

$$(\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisLowerBound.claim}) \Leftrightarrow ((\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \to (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisLowerBound.lowerBound} \le (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) - (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right))))))) \land (\operatorname{IsGLB}\left(\{(s: \mathbb{R}) \mid \exists (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \land (\exists (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \land (s = (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) - (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right))))))\}, \operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisLowerBound.lowerBound}\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

The first clause includes every natural n ≥ 2 and every k : Fin n → ℝ with all coordinates strictly positive. The original skewness and kurtosis use the same vector, with repeated coordinates counted with multiplicity. The IsGLB clause uses exactly the values realized by these finite vectors, with unbounded n. It imposes neither a topology classification nor an abstract-moment realizability assumption.

**Theorem 1.3 (The universal bound and its sharp actual approximation).**

$$(\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (\forall (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \to (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisLowerBound.lowerBound} \le (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) - (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right))))))) \land (\operatorname{IsGLB}\left(\{(s: \mathbb{R}) \mid \exists (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \land (\exists (k: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < k\left(i\right))) \land (s = (\operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness}\left(k\right)) - (\operatorname{D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis}\left(k\right))))))\}, \operatorname{D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisLowerBound.lowerBound}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/ptaszynski-skewness-minus-kurtosis-lower-bound` (proved) by `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ptaszynski-skewness-minus-kurtosis-lower-bound","declaration_gid":"D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Krzysztof Ptaszyński (2022). *Bounds on skewness and kurtosis of steady-state currents*. DOI: [10.1103/PhysRevE.106.024119](https://doi.org/10.1103/PhysRevE.106.024119). URL: <https://arxiv.org/abs/2204.08421v4>.

*Commentary.*

Write Rⱼ = ∑ᵢ kᵢ⁻ʲ. The original definitions are S = 3R₂²/R₁⁴ − 2R₃/R₁³ and K = 15R₂²/R₁⁴ − 20R₃/R₁³ + 6R₄/(R₁²R₂). They are scaled current cumulant ratios C₃/C₁ and C₄/C₂. They are not standardized central moments. The original normalized_simplex and normalized_difference apply to xᵢ = kᵢ⁻¹/R₁. With p = ∑xᵢ², q = ∑xᵢ³, r = ∑xᵢ⁴ and u = √p, they give ∑xᵢ = 1, 0 < p, 0 ≤ xᵢ ≤ u ≤ 1 and D = S − K = −12p² + 18q − 6r/p.

For u ≤ 1/3 the nonnegative sum ∑xᵢ²(u − xᵢ)(u + xᵢ − 3p) equals p[D − f(u)]/6, where f(u) = −12u⁴ + 18u³ − 6u². The factorization f(u) − C = (u − (9 − √17)/16)² [−12u² + (9 + 3√17)u/2 + (15 + 9√17)/32] is nonnegative on this interval. For u ≥ 1/3 put d = (3p − u)/2. The nonnegative sum ∑xᵢ(u − xᵢ)(xᵢ − d)² equals p[D + (3/2)u(1 − u)³]/6. Finally 8/81 − u(1 − u)³ = (u − 1/3)[4/27 + (u − 1/3)(1 − u)(4/3 − u)] ≥ 0, so D ≥ −4/27 ≥ C. These are estimates on the original common finite vector.

For sharpness let α = (9 − √17)/16, which lies strictly between zero and one. For every natural m take n = m + 2 and rates k₀ = 1/α and kᵢ = (m + 1)/(1 − α) for i ≠ 0. All rates are positive and their inverse rates sum to one. For j = 2,3,4 the exact moments are αʲ + (1 − α)ʲ/(m + 1)ʲ⁻¹. With z = 1/(m + 1), the difference is −12[α² + (1 − α)²z]² + 18[α³ + (1 − α)³z²] − 6[α⁴ + (1 − α)⁴z³]/[α² + (1 − α)²z]. The denominator at zero is α² > 0. Continuity and z → 0 give f(α) = C. Every term is an actual value in the asserted set, so every lower bound of that set is at most C.

Dividing these rates by their common tail rate gives exceptional rate a = (1 − α)/(α(N − 1)) = A/(N − 1), with A = (5 + √17)/4. This finite family differs from the source's A/N, and their ratio N/(N − 1) tends to one. The proof directly evaluates its own finite vectors and requires no finite-family identification.

Publication binding: the complete conjunction is the separately preregistered external assertion in issue #25782 (https://github.com/the-omega-institute/trureturing/issues/25782), source-screen Tier 1, source year 2022. The independent source screen establishes source readiness only. The frozen result statement ID is sha256:9e112720537c1dfd894f6dd624b465d17d20bff60039fe4b6d621f10bcb542a8; the actual frozen module ID is sha256:600dd89006d5b3c22e1ed3de8482e0263a19f08afa9c1e2ee752f7b203150ae1. The primary main.tex SHA-256 is 0d8f9bf311a07990b64d4746e9ec4fb1e164deec23b270503642b94766baf84e.

All eight theorem declarations have proof_shape: bind-only under the repository normalization rule; this is a semantic assessment, not a machine classification. The seven live helper consumers are: polynomial_lower_bound and coarse_lower_bound feed simplex_lower_bound; simplex_lower_bound feeds universal_lower_bound; universal_lower_bound feeds result; sharp_rates_positive feeds sharp_limit and result; sharp_value feeds sharp_limit; sharp_limit feeds result. The terminal result's intended admission_basis is open-problem-resolution; utility: none. Helpers organize the proof and receive no independent content or resolution credit; no escape witness is claimed. Its axiom closure is Classical.choice, Quot.sound and propext, with no new axiom or sorry. Existing common-vector normalization and moment extraction are reused.

The owning Reg reconstructs the whole claim with Params = Nat, State N = Fin N → ℝ and Output = ℝ through the existing DependentFamily enrollment. The actual law, variation, sensitivity and observational binding concern this entire family, including N = 2; no fixed-N surrogate is substituted. Its current binding is fb9829368b277c193c04d46777f8acb16d60e534c6c9a3dcff784d7e2bb8b245; familyRecord = none and continuation = unknown, which asserts neither undecidability nor inexhaustibility. The result claims neither strict finite inequality nor finite-N optimizer classification.

The bounded literature check covered exact arXiv metadata and independently retrieved 2305.09759v1, 2411.19643v3 and 2610.12652v1 without identifying settlement of this target. Citation-list retrieval from OpenAlex and Semantic Scholar returned 429; unauthenticated code search and the journal PDF returned 401. Loogle, LeanSearch and Reservoir coverage was not completed. These are search limitations, not no-hit evidence. Generic pinned Mathlib normalization, positive sums, moments, reciprocal limits and GLB interfaces are reused; the Mathlib revision is 56a005855ea17e0b0958f73ec801ae140b0a1679.

For N = 2 the interpretation is two oriented, channel-labelled phase stages with one marked winding crossing; that physical identification is not explicitly supplied by the source notation. The theorem proves the rational inverse-rate expressions; it constructs no stochastic process, renewal identification or empirical correspondence. Physical N = 1, bidirectional, thermal and multicyclic networks and finite-time cumulants are outside its scope. Bounded source and literature searches do not establish worldwide openness or priority.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound.lowerBound`
- Truth anchor: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound.result`
- Dependency: [D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound](UnicyclicSkewnessMinusKurtosisUpperBound.md)

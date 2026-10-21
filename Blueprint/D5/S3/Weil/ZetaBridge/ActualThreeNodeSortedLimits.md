# Actual three-node SortedLimits

## Abstract

Actual three-node SortedLimits

For c>=3 the existing prime-symbol mean lower bound gives mu>=0; hence h=(pi/4)^2+mu>0 and (pi/4)^2+4mu>0. These facts and n!=0 prove positivity of the final smallest constants in both arithmetic branches.

The scalar factors l_N and u_N both tend to one. One natural cutoff, chosen using only c and n, ensures N>=9, N>|n|, N>delta, l_N>0 and u_N>0 before every vector and every sorted index.

The existing eigenvalues_zero_mono and eigenvalues_zero_smul theorems convert the actual full336 Loewner bounds into l_N lambda_i(H_N) <= pi^2 N lambda_i(K_N) <= u_N lambda_i(H_N). All scaling coefficients passed to the sorting API are nonnegative.

For any one proved finite limit N^e lambda_i(H_N)->L, multiplication by the nonnegative factor N^e/pi^2 and scalar squeeze give N^(e+1) lambda_i(K_N)->L/pi^2. This is applied to each of the three literal sorted indices.

If a=arithmeticBoundarySymbol(c,n)!=0, the actual complete-tail limits for N lambda_0, N lambda_1 and N^3 lambda_2 are max(6h,4a^2)/pi^2, min(6h,4a^2)/pi^2 and n^2 a^2((pi/4)^2+4mu)/(9pi^2 h).

If a=0, the actual complete-tail limits for N lambda_0, N^3 lambda_1 and N^5 lambda_2 are 6h/pi^2, 4h n^2/(3pi^2) and 16h n^4/(135pi^2). These are sorted eigenvalues of the sealed original complex source Gram.

These statements concern the complete three-column tail Gram in the original retained Euclidean metric. Full physical Weil positivity, middle/complement/fullSchur control, EF/cofinal steps, Robin and RH require further proofs.

**Theorem 1.1 (actual mean nonneg).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_mean_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_mean_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_mean_nonneg {c : ℕ} (hc : 3 ≤ c) : 0 ≤ mean c

**Theorem 1.2 (actual h pos).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_h_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_h_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_h_pos {c : ℕ} (hc : 3 ≤ c) : 0 < (Real.pi / 4) ^ 2 + mean c

**Theorem 1.3 (actual gmu pos).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_gmu_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_gmu_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_gmu_pos {c : ℕ} (hc : 3 ≤ c) : 0 < (Real.pi / 4) ^ 2 + 4 * mean c

**Theorem 1.4 (actual last constants pos).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_last_constants_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_last_constants_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_last_constants_pos {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0) :     0 < 16 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 4 / (135 * Real.pi ^ 2) ∧     (arithmeticBoundarySymbol c n ≠ 0 →       0 < (n : ℝ) ^ 2 * (arithmeticBoundarySymbol c n) ^ 2 *         ((Real.pi / 4) ^ 2 + 4 * mean c) /         (9 * Real.pi ^ 2 * ((Real.pi / 4) ^ 2 + mean c)))

**Theorem 1.5 (actual nonzero eventual roots pos).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_nonzero_eventual_roots_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_nonzero_eventual_roots_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

lemma actual_nonzero_eventual_roots_pos {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)     (ha : arithmeticBoundarySymbol c n ≠ 0) :     ∀ᶠ N : ℕ in atTop,       0 < rhoPlus (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) ∧       0 < O (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N) ∧       0 < rhoMinus (Real.pi / 4) (mean c) (arithmeticBoundarySymbol c n) ((n : ℝ) / N)

**Theorem 1.6 (relative factor limits).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.relative_factor_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.relative_factor_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem relative_factor_limits (c : ℕ) (n : ℤ) :     Tendsto (lower336 c) atTop (𝓝 1) ∧       Tendsto (fun N : ℕ => upper336 c N n) atTop (𝓝 1)

**Theorem 1.7 (actual admissible cutoff).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_admissible_cutoff`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_admissible_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_admissible_cutoff (c : ℕ) (n : ℤ) :     ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →       9 ≤ N ∧ |(n : ℝ)| < (N : ℝ) ∧ delta336 c < (N : ℝ) ∧         0 < lower336 c N ∧ 0 < upper336 c N n

**Definition 1.8 (actualEigen).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actualEigen`

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actualEigen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

abbrev actualEigen {c : ℕ} (hc : 3 ≤ c) (n : ℤ) (N : ℕ) : Fin 3 → ℝ :=   (show (actualTailGram hc n N).IsHermitian from Matrix.isHermitian_gram _ _).eigenvalues₀

**Theorem 1.9 (actual sorted relative bounds).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_sorted_relative_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_sorted_relative_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_sorted_relative_bounds {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)     (N : ℕ) (hN9 : 9 ≤ N) (hR : |(n : ℝ)| < (N : ℝ))     (hl : 0 ≤ lower336 c N) (hu : 0 ≤ upper336 c N n) (i : Fin 3) :     lower336 c N * finiteEigen (Real.pi / 4) (mean c)         (arithmeticBoundarySymbol c n) ((n : ℝ) / N) i ≤       (Real.pi ^ 2 * N) * actualEigen hc n N i ∧     (Real.pi ^ 2 * N) * actualEigen hc n N i ≤       upper336 c N n * finiteEigen (Real.pi / 4) (mean c)         (arithmeticBoundarySymbol c n) ((n : ℝ) / N) i

**Theorem 1.10 (actual nonzero sorted limits).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_nonzero_sorted_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_nonzero_sorted_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_nonzero_sorted_limits {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)     (ha : arithmeticBoundarySymbol c n ≠ 0) :     Tendsto (fun N : ℕ => (N : ℝ) * actualEigen hc n N 0) atTop       (𝓝 (max (6 * ((Real.pi / 4) ^ 2 + mean c))         (4 * (arithmeticBoundarySymbol c n) ^ 2) / Real.pi ^ 2)) ∧     Tendsto (fun N : ℕ => (N : ℝ) * actualEigen hc n N 1) atTop       (𝓝 (min (6 * ((Real.pi / 4) ^ 2 + mean c))         (4 * (arithmeticBoundarySymbol c n) ^ 2) / Real.pi ^ 2)) ∧     Tendsto (fun N : ℕ => (N : ℝ) ^ 3 * actualEigen hc n N 2) atTop       (𝓝 ((n : ℝ) ^ 2 * (arithmeticBoundarySymbol c n) ^ 2 *         ((Real.pi / 4) ^ 2 + 4 * mean c) /         (9 * Real.pi ^ 2 * ((Real.pi / 4) ^ 2 + mean c)))) ∧     0 < (n : ℝ) ^ 2 * (arithmeticBoundarySymbol c n) ^ 2 *         ((Real.pi / 4) ^ 2 + 4 * mean c) /         (9 * Real.pi ^ 2 * ((Real.pi / 4) ^ 2 + mean c))

**Theorem 1.11 (actual zero sorted limits).**

Lean statement: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_zero_sorted_limits`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_zero_sorted_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

theorem actual_zero_sorted_limits {c : ℕ} (hc : 3 ≤ c) {n : ℤ} (hn : n ≠ 0)     (ha : arithmeticBoundarySymbol c n = 0) :     Tendsto (fun N : ℕ => (N : ℝ) * actualEigen hc n N 0) atTop       (𝓝 (6 * ((Real.pi / 4) ^ 2 + mean c) / Real.pi ^ 2)) ∧     Tendsto (fun N : ℕ => (N : ℝ) ^ 3 * actualEigen hc n N 1) atTop       (𝓝 (4 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 2 / (3 * Real.pi ^ 2))) ∧     Tendsto (fun N : ℕ => (N : ℝ) ^ 5 * actualEigen hc n N 2) atTop       (𝓝 (16 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 4 / (135 * Real.pi ^ 2))) ∧     0 < 16 * ((Real.pi / 4) ^ 2 + mean c) * (n : ℝ) ^ 4 / (135 * Real.pi ^ 2)

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actualEigen`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_admissible_cutoff`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_gmu_pos`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_h_pos`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_last_constants_pos`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_mean_nonneg`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_nonzero_eventual_roots_pos`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_nonzero_sorted_limits`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_sorted_relative_bounds`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.actual_zero_sorted_limits`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualThreeNodeSortedLimits.relative_factor_limits`
- Dependency: [D5/S3/Quantum/Schatten/SingularValueOrder](../../Quantum/Schatten/SingularValueOrder.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteLimits](ActualThreeNodeFiniteLimits.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualThreeNodeFull336](ActualThreeNodeFull336.md)

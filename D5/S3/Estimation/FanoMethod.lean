/- GID: D5/S3/Estimation/FanoMethod
   generality: I
   mirror-B: D5/B/S3/Estimation/FanoMethod
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive Fano's method from uniform-mixture KL averaging and finite Fano. -/

import D5.S3.Estimation.FanoReferenceDivergence

/-!
# Fano's method

For a uniform finite family of observation laws, joint KL divergence to a common reference is the
average of the candidate-wise divergences. This cancellation identity is the substantive step:
the hidden marginal is first derived from the mixture hypothesis, then the common inverse-cardinal
factor cancels inside each logarithm. The mutual-information and minimax bounds that follow are
compositions of this identity with the frozen any-reference and counting forms of Fano.
-/

/- Library-search audit trail (2026-08-12):
   * Pinned mathlib searches covered Fano, minimax lower bounds, KL diameter/averaging, and
     mutual-information reference bounds. No matching finite real-valued Fano-method theorem was
     found. Reused algebra/order facts include `Finset.sum_le_sum`, `Finset.sum_le_card_nsmul`,
     `Fintype.sum_prod_type`, `Real.log_pos`, `Real.log_pow`, `Real.log_two_gt_d9`, and
     `le_div_iff₀`.
   * The actual working tree under `D5/` was searched for mixture constructions, averaged
     `klDivergence`, average-reference mutual-information bounds, minimax statements, and
     KL-diameter statements. No requested result was found; the only relevant matches were the
     frozen demon/reference-divergence ingredients consumed below.
-/

namespace D5.S3.Estimation.FanoMethod

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.MutualInformation
open D5.S3.Estimation.FanoDivergenceForm
open D5.S3.Estimation.FanoReferenceDivergence

open Classical in
/-- Joint divergence of a uniform mixture to a common-reference product is the average of the
candidate-wise divergences. The hidden marginal is a consequence of `hmix` and normalization of
the candidate laws, rather than an additional hypothesis. -/
theorem kl_divergence_uniform_mixture_eq_average
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1) :
    klDivergence p
        (fun z => Q z.1 * marginal (fun r : X × Y => p (r.2, r.1)) z.2) =
      (Fintype.card X : ℝ)⁻¹ * ∑ i, klDivergence (P i) Q := by
  classical
  have hQ_distribution : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1 :=
    ⟨fun y => (hQ y).le, hQ_sum⟩
  letI : Nonempty X := by
    by_contra hX
    letI : IsEmpty X := not_nonempty_iff.mp hX
    simpa using hp.2
  have hcard_pos : 0 < Fintype.card X := Fintype.card_pos_iff.mpr inferInstance
  have hcard_cast_ne : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast hcard_pos.ne'
  have hmarginal (i : X) :
      marginal (fun r : X × Y => p (r.2, r.1)) i =
        (Fintype.card X : ℝ)⁻¹ := by
    rw [marginal]
    calc
      (∑ y, p (y, i)) =
          ∑ y, (Fintype.card X : ℝ)⁻¹ * P i y := by
            apply Finset.sum_congr rfl
            intro y _
            exact hmix (y, i)
      _ = (Fintype.card X : ℝ)⁻¹ * ∑ y, P i y := by
            rw [Finset.mul_sum]
      _ = (Fintype.card X : ℝ)⁻¹ := by rw [(hP i).2, mul_one]
  have hratio (y : Y) (i : X) :
      (Fintype.card X : ℝ)⁻¹ * P i y /
          (Q y * (Fintype.card X : ℝ)⁻¹) =
        P i y / Q y := by
    field_simp [hcard_cast_ne, (hQ y).ne']
  simp only [klDivergence, Fintype.sum_prod_type]
  calc
    (∑ y, ∑ i,
        p (y, i) *
          Real.log
            (p (y, i) /
              (Q y * marginal (fun r : X × Y => p (r.2, r.1)) i))) =
        ∑ y, ∑ i,
          (Fintype.card X : ℝ)⁻¹ *
            (P i y * Real.log (P i y / Q y)) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro i _
      rw [hmix (y, i), hmarginal i, hratio]
      ring
    _ = ∑ i, ∑ y,
          (Fintype.card X : ℝ)⁻¹ *
            (P i y * Real.log (P i y / Q y)) := by
      rw [Finset.sum_comm]
    _ = ∑ i, (Fintype.card X : ℝ)⁻¹ *
          ∑ y, P i y * Real.log (P i y / Q y) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = (Fintype.card X : ℝ)⁻¹ *
          ∑ i, ∑ y, P i y * Real.log (P i y / Q y) := by
      rw [Finset.mul_sum]

open Classical in
/-- Mutual information is bounded by the average candidate divergence to any common strictly
positive normalized reference. -/
theorem mutual_information_le_average_reference_divergence
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1) :
    mutualInformation p ≤
      (Fintype.card X : ℝ)⁻¹ * ∑ i, klDivergence (P i) Q := by
  exact
    (mutual_information_le_product_reference_divergence p Q hp hQ hQ_sum).trans_eq
      (kl_divergence_uniform_mixture_eq_average
        p P Q hp hP hQ hQ_sum hmix)

open Classical in
/-- If every candidate is within divergence `D` of the common reference, then the average bound
relaxes to the uniform information budget `D`. -/
theorem mutual_information_le_uniform_reference_divergence
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ) (D : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ D) :
    mutualInformation p ≤ D := by
  classical
  letI : Nonempty X := by
    by_contra hX
    letI : IsEmpty X := not_nonempty_iff.mp hX
    simpa using hp.2
  have hcard_pos : 0 < Fintype.card X := Fintype.card_pos_iff.mpr inferInstance
  have hcard_cast_ne : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast hcard_pos.ne'
  have hsum : (∑ i, klDivergence (P i) Q) ≤ ∑ _ : X, D :=
    Finset.sum_le_sum fun i _ => hdiv i
  calc
    mutualInformation p ≤
        (Fintype.card X : ℝ)⁻¹ * ∑ i, klDivergence (P i) Q :=
      mutual_information_le_average_reference_divergence
        p P Q hp hP hQ hQ_sum hmix
    _ ≤ (Fintype.card X : ℝ)⁻¹ * ∑ _ : X, D :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (by positivity))
    _ = D := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      field_simp [hcard_cast_ne]

open Classical in
/-- Fano's method in product form. For an arbitrary estimator, small error would require more
information than a uniformly `D`-close family supplies. -/
theorem fano_method_minimax_product_bound
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ)
    (g : Y → X) (D ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ D)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε) :
    (1 - ε) * Real.log (Fintype.card X) ≤ D + Real.log 2 := by
  classical
  have huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹ := by
    funext i
    rw [marginal]
    calc
      (∑ y, p (y, i)) =
          ∑ y, (Fintype.card X : ℝ)⁻¹ * P i y := by
            apply Finset.sum_congr rfl
            intro y _
            exact hmix (y, i)
      _ = (Fintype.card X : ℝ)⁻¹ * ∑ y, P i y := by
            rw [Finset.mul_sum]
      _ = (Fintype.card X : ℝ)⁻¹ := by rw [(hP i).2, mul_one]
  have hmi : mutualInformation p ≤ D :=
    mutual_information_le_uniform_reference_divergence
      p P Q D hp hP hQ hQ_sum hmix hdiv
  have hbudget : mutualInformation p + Real.log 2 ≤ D + Real.log 2 := by
    linarith
  exact
    (fano_hypothesis_count_product_bound_uniform
      p g ε hp huniform herror).trans hbudget

open Classical in
/-- Solved error form of Fano's method. The cardinality condition is exactly what makes the
logarithmic denominator positive, so division preserves the inequality. -/
theorem fano_method_minimax_error_lower_bound
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ)
    (g : Y → X) (D ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ D)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε)
    (hX : 2 ≤ Fintype.card X) :
    1 - (D + Real.log 2) / Real.log (Fintype.card X) ≤ ε := by
  have hproduct :=
    fano_method_minimax_product_bound
      p P Q g D ε hp hP hQ hQ_sum hmix hdiv herror
  have hcard_real_gt_one : (1 : ℝ) < Fintype.card X := by
    exact_mod_cast (show 1 < Fintype.card X by omega)
  have hlog_pos : 0 < Real.log (Fintype.card X) :=
    Real.log_pos hcard_real_gt_one
  have hratio :
      1 - ε ≤ (D + Real.log 2) / Real.log (Fintype.card X) :=
    (le_div_iff₀ hlog_pos).2 hproduct
  linarith

open Classical in
/-- Informative four-candidate instance. Divergence at most `1/10` forces every estimator with
error upper bound `ε` to satisfy the specialized product bound and, numerically, `0.427865 < ε`.
Thus the exact lower floor is approximately `42.7865%`, conventionally reported as `42.8%`. -/
theorem fano_method_four_candidates_informative
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ)
    (g : Y → X) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1)
    (hcard : Fintype.card X = 4)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ (1 / 10 : ℝ))
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε) :
    (1 - ε) * Real.log 4 ≤ (1 / 10 : ℝ) + Real.log 2 ∧
      (0.427865 : ℝ) < ε := by
  have hX : 2 ≤ Fintype.card X := by omega
  have hproduct :=
    fano_method_minimax_product_bound
      p P Q g (1 / 10 : ℝ) ε hp hP hQ hQ_sum hmix hdiv herror
  have hbound :=
    fano_method_minimax_error_lower_bound
      p P Q g (1 / 10 : ℝ) ε hp hP hQ hQ_sum hmix hdiv herror hX
  rw [hcard] at hproduct hbound
  refine ⟨hproduct, ?_⟩
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hden : 0 < 2 * Real.log 2 := mul_pos (by norm_num) hlog_two_pos
  have hratio :
      ((1 / 10 : ℝ) + Real.log 2) / (2 * Real.log 2) <
        1 - (0.427865 : ℝ) := by
    rw [div_lt_iff₀ hden]
    nlinarith [Real.log_two_gt_d9]
  norm_num at hbound
  rw [hlog_four] at hbound
  linarith

/-- Vacuous four-candidate instance. At budget `D = log 4`, both the product form and its solved
lower floor hold for every nonnegative `ε`; the solved floor is exactly `-1/2`, so it imposes no
constraint on an error probability. -/
theorem fano_method_four_candidates_vacuous
    (ε : ℝ) (hε : 0 ≤ ε) :
    (1 - ε) * Real.log 4 ≤ Real.log 4 + Real.log 2 ∧
      1 - (Real.log 4 + Real.log 2) / Real.log 4 ≤ ε := by
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_two_ne : Real.log 2 ≠ 0 := hlog_two_pos.ne'
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  constructor
  · rw [hlog_four]
    nlinarith [mul_nonneg hε hlog_two_pos.le]
  · have hfloor :
        1 - (Real.log 4 + Real.log 2) / Real.log 4 = -(1 / 2 : ℝ) := by
      rw [hlog_four]
      field_simp [hlog_two_ne]
      ring
    rw [hfloor]
    linarith

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1) :
    klDivergence p
        (fun z => Q z.1 * marginal (fun r : X × Y => p (r.2, r.1)) z.2) =
      (Fintype.card X : ℝ)⁻¹ * ∑ i, klDivergence (P i) Q := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact kl_divergence_uniform_mixture_eq_average
    p P Q hp hP hQ hQ_sum hmix

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1) :
    mutualInformation p ≤
      (Fintype.card X : ℝ)⁻¹ * ∑ i, klDivergence (P i) Q := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact mutual_information_le_average_reference_divergence
    p P Q hp hP hQ hQ_sum hmix

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ) (D : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ D) :
    mutualInformation p ≤ D := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact mutual_information_le_uniform_reference_divergence
    p P Q D hp hP hQ hQ_sum hmix hdiv

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ)
    (g : Y → X) (D ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ D)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε) :
    (1 - ε) * Real.log (Fintype.card X) ≤ D + Real.log 2 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact fano_method_minimax_product_bound
    p P Q g D ε hp hP hQ hQ_sum hmix hdiv herror

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ)
    (g : Y → X) (D ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ D)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε)
    (hX : 2 ≤ Fintype.card X) :
    1 - (D + Real.log 2) / Real.log (Fintype.card X) ≤ ε := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact fano_method_minimax_error_lower_bound
    p P Q g D ε hp hP hQ hQ_sum hmix hdiv herror hX

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (P : X → Y → ℝ) (Q : Y → ℝ)
    (g : Y → X) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hP : ∀ i, (∀ y, 0 ≤ P i y) ∧ ∑ y, P i y = 1)
    (hQ : ∀ y, 0 < Q y) (hQ_sum : ∑ y, Q y = 1)
    (hmix : ∀ z : Y × X, p z = (Fintype.card X : ℝ)⁻¹ * P z.2 z.1)
    (hcard : Fintype.card X = 4)
    (hdiv : ∀ i, klDivergence (P i) Q ≤ (1 / 10 : ℝ))
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε) :
    (1 - ε) * Real.log 4 ≤ (1 / 10 : ℝ) + Real.log 2 ∧
      (0.427865 : ℝ) < ε := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact fano_method_four_candidates_informative
    p P Q g ε hp hP hQ hQ_sum hmix hcard hdiv herror

example (ε : ℝ) (hε : 0 ≤ ε) :
    (1 - ε) * Real.log 4 ≤ Real.log 4 + Real.log 2 ∧
      1 - (Real.log 4 + Real.log 2) / Real.log 4 ≤ ε := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact fano_method_four_candidates_vacuous ε hε

#print axioms kl_divergence_uniform_mixture_eq_average
#print axioms mutual_information_le_average_reference_divergence
#print axioms mutual_information_le_uniform_reference_divergence
#print axioms fano_method_minimax_product_bound
#print axioms fano_method_minimax_error_lower_bound
#print axioms fano_method_four_candidates_informative
#print axioms fano_method_four_candidates_vacuous

end D5.S3.Estimation.FanoMethod

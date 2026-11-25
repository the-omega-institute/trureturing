/- GID: D5/S3/Fourier/Concentration/DisjointCharacterRemainder
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/DisjointCharacterRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conjugate phases give signed overlap squares with a degree-sensitive remainder. -/

import D5.S3.Fourier.Concentration.DisjointCharacterEnvelope

/-! Signed overlap contributions and coefficientwise estimates for conjugate phases. -/

open Finset PowerSeries
open scoped PowerSeries ComplexConjugate

noncomputable section

namespace D5.S3.Fourier.Concentration.DisjointCharacterRemainder

open DisjointCharacterEnvelope

private def realAxis (z : ℝ) : ℝ⟦X⟧ := rescale z (PowerSeries.exp ℝ)

private theorem realAxis_coeff (z : ℝ) (n : ℕ) :
    coeff n (realAxis z) = z ^ n / n.factorial := by
  simp [realAxis, coeff_exp, div_eq_mul_inv]

private theorem realAxis_mul (a b : ℝ) : realAxis a * realAxis b = realAxis (a + b) :=
  exp_mul_exp_eq_exp_add a b

private theorem coeff_mul_majorized (P Q : ℂ⟦X⟧) (U V : ℝ⟦X⟧)
    (hP : ∀ n, ‖coeff n P‖ ≤ coeff n U) (hQ : ∀ n, ‖coeff n Q‖ ≤ coeff n V) (n : ℕ) :
    ‖coeff n (P * Q)‖ ≤ coeff n (U * V) := by
  rw [coeff_mul, coeff_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hP i.1) (hQ i.2) (norm_nonneg _) ((norm_nonneg _).trans (hP i.1))

private def tailMajorant (a : ℂ) : ℝ⟦X⟧ := C ‖a‖ * (X * realAxis ‖a‖)

private theorem tail_majorized (a : ℂ) (n : ℕ) :
    ‖coeff n (axis (-a) - 1)‖ ≤ coeff n (tailMajorant a) := by
  rw [tailMajorant, coeff_C_mul, ← pow_one (X : ℝ⟦X⟧), coeff_X_pow_mul']
  cases n with
  | zero =>
    have hzero : coeff 0 (axis (-a)) = 1 := by
      rw [axis, coeff_rescale, coeff_exp]
      simp
    simp only [map_sub, hzero, coeff_one, ite_true, sub_self, norm_zero,
      show ¬ (1 : ℕ) ≤ 0 by omega, ite_false, mul_zero, le_refl]
  | succ n =>
    simp only [map_sub, coeff_one, Nat.succ_ne_zero, ite_false, sub_zero, axis_norm_coeff,
      norm_neg, show 1 ≤ n + 1 by omega, ite_true, Nat.succ_sub_one, realAxis_coeff]
    rw [pow_succ', ← mul_div_assoc]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))

/-- The univariate coefficient on the subset selected in the overlap expansion. -/
def overlapCoefficient {J : Type*} (t : Finset J) (c : ℂ) (a : J → ℂ) (d : ℕ) : ℂ :=
  coeff d (axis c * ∏ j ∈ t, (axis (-a j) - 1))

private theorem product_majorized {J : Type*} (t : Finset J) (a : J → ℂ) (c : ℂ) (d : ℕ) :
    ‖overlapCoefficient t c a d‖ ≤ coeff d (realAxis ‖c‖ * ∏ j ∈ t, tailMajorant (a j)) := by
  classical
  have hp : ∀ n, ‖coeff n (∏ j ∈ t, (axis (-a j) - 1))‖ ≤
      coeff n (∏ j ∈ t, tailMajorant (a j)) := by
    induction t using Finset.induction_on with
    | empty => intro n; by_cases hn : n = 0 <;> simp [hn]
    | insert j t hj ih =>
      intro n
      rw [prod_insert hj, prod_insert hj]
      exact coeff_mul_majorized _ _ _ _ (tail_majorized (a j)) ih n
  exact coeff_mul_majorized _ _ _ _ (fun n => by rw [axis_norm_coeff, realAxis_coeff]) hp d

private theorem product_majorant_eq {J : Type*} (t : Finset J) (a : J → ℂ) (c : ℝ) :
    realAxis c * ∏ j ∈ t, tailMajorant (a j) =
      C (∏ j ∈ t, ‖a j‖) * (X ^ t.card * realAxis (c + ∑ j ∈ t, ‖a j‖)) := by
  classical
  induction t using Finset.induction_on generalizing c with
  | empty => simp
  | insert j t hj ih =>
    rw [prod_insert hj, prod_insert hj, sum_insert hj, card_insert_of_notMem hj, tailMajorant]
    calc
      _ = C ‖a j‖ * X * (realAxis (c + ‖a j‖) * ∏ k ∈ t, tailMajorant (a k)) := by
        rw [← realAxis_mul]; ring
      _ = _ := by
        rw [ih, map_mul, pow_succ, add_assoc c ‖a j‖]
        ring

private theorem shifted_coefficient_bound {J : Type*} (t : Finset J) (c : ℂ) (a : J → ℂ) (d : ℕ) :
    ‖overlapCoefficient t c a d‖ ≤
      if t.card ≤ d then (∏ j ∈ t, ‖a j‖) * (‖c‖ + ∑ j ∈ t, ‖a j‖) ^ (d - t.card) /
        ((d - t.card).factorial : ℝ) else 0 := by
  have h := product_majorized t a c d
  rw [product_majorant_eq, coeff_C_mul, coeff_X_pow_mul'] at h
  split_ifs at h ⊢ with hd
  · simpa only [realAxis_coeff, mul_div_assoc] using h
  · simpa using h

private theorem conj_axis (z : ℂ) : PowerSeries.map (starRingEnd ℂ) (axis z) = axis (conj z) := by
  rw [axis, axis, ← PowerSeries.map_exp (f := starRingEnd ℂ)]
  ext n
  simp [coeff_rescale, coeff_map]

private theorem conjugate_tail (a : ℂ) :
    (1 - axis (-conj a)) = -(PowerSeries.map (starRingEnd ℂ) (axis (-a) - 1)) := by
  rw [map_sub, map_one, conj_axis, map_neg, neg_sub]

private theorem overlap_conjugate {J : Type*} (t : Finset J) (c : ℂ) (a : J → ℂ) (d : ℕ) :
    coeff d (axis (conj c) * ∏ j ∈ t, (1 - axis (-conj (a j)))) =
      (-1 : ℂ) ^ t.card * conj (overlapCoefficient t c a d) := by
  have hp : (∏ j ∈ t, (1 - axis (-conj (a j)))) =
      C ((-1 : ℂ) ^ t.card) * PowerSeries.map (starRingEnd ℂ) (∏ j ∈ t, (axis (-a j) - 1)) := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | insert j t hj ih =>
      simp only [prod_insert hj, card_insert_of_notMem hj, pow_succ, map_mul, map_neg,
        map_one, ih]
      rw [conjugate_tail]
      ring
  rw [hp]
  calc
    _ = coeff d (C ((-1 : ℂ) ^ t.card) *
        PowerSeries.map (starRingEnd ℂ) (axis c * ∏ j ∈ t, (axis (-a j) - 1))) := by
      congr 1
      rw [map_mul, conj_axis]
      ring
    _ = _ := by rw [coeff_C_mul, coeff_map, overlapCoefficient]

/-- The mixed coefficient is an alternating sum of real squares, with a
finite degree-dependent majorant for each square root. -/
theorem signed_overlap_expansion {J : Type*} (s : Finset J) (a : J → ℂ) (d : ℕ) :
    let c := ∑ j ∈ s, a j
    let magnitude := fun z : ℂ => ‖z‖
    coeff d (coeff d (disjointSeries s a (fun j => conj (a j)))) =
      ((∑ t ∈ s.powerset.filter (fun t => t.card ≤ d),
        (-1 : ℝ) ^ t.card * magnitude (overlapCoefficient t c a d) ^ 2) : ℂ) ∧
    ∀ t ⊆ s, magnitude (overlapCoefficient t c a d) ≤
      if t.card ≤ d then (∏ j ∈ t, ‖a j‖) * (‖c‖ + ∑ j ∈ t, ‖a j‖) ^ (d - t.card) /
        ((d - t.card).factorial : ℝ) else 0 := by
  classical
  dsimp only
  constructor
  · rw [split_product]
    simp only [map_sum, coeff_onBoth]
    rw [← map_sum (starRingEnd ℂ)]
    trans ∑ t ∈ s.powerset, ((-1 : ℂ) ^ t.card *
        (‖overlapCoefficient t (∑ j ∈ s, a j) a d‖ : ℂ) ^ 2)
    · apply sum_congr rfl
      intro t ht
      rw [overlap_conjugate, ← overlapCoefficient]
      rw [mul_left_comm, Complex.mul_conj']
    · push_cast
      refine (sum_subset (filter_subset _ _) ?_).symm
      intro t ht hnot
      have hd : ¬ t.card ≤ d := by
        intro h
        exact hnot (mem_filter.mpr ⟨ht,h⟩)
      have hnorm := shifted_coefficient_bound t (∑ j ∈ s, a j) a d
      rw [ite_eq_right hd] at hnorm
      have hz := norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
      simp [hz]
  · intro t _
    exact shifted_coefficient_bound t _ a d

/-- In a truncated signed expansion, only the even omitted subsets contribute to the
upper error bound and only the odd subsets contribute to the lower error bound. -/
theorem signed_overlap_remainder {J : Type*} (s : Finset J) (a : J → ℂ) (d K : ℕ) :
    let c := ∑ j ∈ s, a j
    let squareNorm := fun z : ℂ => ‖z‖ ^ 2
    let admissible := s.powerset.filter (fun t => t.card ≤ d)
    let small := admissible.filter (fun t => t.card ≤ K)
    let large := admissible.filter (fun t => K < t.card)
    let square := fun t => squareNorm (overlapCoefficient t c a d)
    let bound := fun t => ((∏ j ∈ t, ‖a j‖) * (‖c‖ + ∑ j ∈ t, ‖a j‖) ^ (d - t.card) /
        ((d - t.card).factorial : ℝ)) ^ 2
    let remainder := (coeff d (coeff d (disjointSeries s a (fun j => conj (a j))))).re -
      ∑ t ∈ small, (-1 : ℝ) ^ t.card * square t
    remainder = (∑ t ∈ large.filter (fun t => Even t.card), square t) -
      (∑ t ∈ large.filter (fun t => ¬ Even t.card), square t) ∧
    -(∑ t ∈ large.filter (fun t => ¬ Even t.card), bound t) ≤ remainder ∧
    remainder ≤ ∑ t ∈ large.filter (fun t => Even t.card), bound t := by
  classical
  intro c squareNorm admissible small large square bound remainder
  have h := signed_overlap_expansion s a d
  have hfull := congrArg Complex.re h.1
  simp only [Complex.re_sum, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re] at hfull
  change (coeff d (coeff d (disjointSeries s a (fun j => conj (a j))))).re =
    (∑ t ∈ admissible, (-1 : ℝ) ^ t.card * square t) at hfull
  have hsplit : (∑ t ∈ admissible, (-1 : ℝ) ^ t.card * square t) =
      (∑ t ∈ small, (-1 : ℝ) ^ t.card * square t) +
      (∑ t ∈ large, (-1 : ℝ) ^ t.card * square t) := by
    simpa only [small, large, not_le] using
      (sum_filter_add_sum_filter_not admissible (fun t => t.card ≤ K)
        (fun t => (-1 : ℝ) ^ t.card * square t)).symm
  have hremain : remainder = ∑ t ∈ large, (-1 : ℝ) ^ t.card * square t := by
    dsimp only [remainder]
    rw [hfull, hsplit, add_sub_cancel_left]
  have hpart : (∑ t ∈ large, (-1 : ℝ) ^ t.card * square t) =
      (∑ t ∈ large.filter (fun t => Even t.card), square t) -
      (∑ t ∈ large.filter (fun t => ¬ Even t.card), square t) := by
    rw [← sum_filter_add_sum_filter_not large (fun t => Even t.card)]
    congr 1
    · exact sum_congr rfl (fun t ht => by rw [(mem_filter.mp ht).2.neg_one_pow, one_mul])
    · rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro t ht
      have ho := (Nat.even_or_odd t.card).resolve_left (mem_filter.mp ht).2
      rw [ho.neg_one_pow, neg_one_mul]
  have hbound : ∀ t ∈ large, square t ≤ bound t := by
    intro t ht
    have ha := mem_filter.mp (mem_filter.mp ht).1
    have hle := h.2 t (mem_powerset.mp ha.1)
    rw [ite_eq_left ha.2] at hle
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hE := sum_le_sum (s := large.filter (fun t => Even t.card))
    (fun t ht => hbound t (mem_filter.mp ht).1)
  have hO := sum_le_sum (s := large.filter (fun t => ¬ Even t.card))
    (fun t ht => hbound t (mem_filter.mp ht).1)
  have hEn : 0 ≤ ∑ t ∈ large.filter (fun t => Even t.card), square t :=
    sum_nonneg fun t _ => sq_nonneg _
  have hOn : 0 ≤ ∑ t ∈ large.filter (fun t => ¬ Even t.card), square t :=
    sum_nonneg fun t _ => sq_nonneg _
  rw [hremain, hpart]
  exact ⟨rfl, by linarith, by linarith⟩

#print axioms signed_overlap_expansion
#print axioms signed_overlap_remainder

end D5.S3.Fourier.Concentration.DisjointCharacterRemainder

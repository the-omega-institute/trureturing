/- GID: D5/S3/Combinatorics/Graph/LegalWords/ActivityMeanCorrespondence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/ActivityMeanCorrespondence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interior path means reconstruct positive site activities and their partition function. -/

import D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence

open scoped BigOperators
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (adm_iff_no_adjacent_true)
open D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion

noncomputable section

/-- The empty-empty remainder on the edge from i to i+1. -/
def seam (u : ℕ → ℝ) (i : ℕ) : ℝ := 1 - u i - u (i + 1)

/-- Activities reconstructed from the means, including both boundary cancellations. -/
def activity (u : ℕ → ℝ) (n : ℕ) : Fin (n + 2) → ℝ :=
  Fin.cons (u 0 / seam u 0)
    (Fin.snoc (fun i : Fin n =>
      u (i.val + 1) * (1 - u (i.val + 1)) / (seam u i.val * seam u (i.val + 1)))
      (u (n + 1) / seam u n))

/-- The product of the occupied site activities. -/
def monomial {N : ℕ} (w : Fin N → ℝ) (b : Fin N → Bool) : ℝ :=
  ∏ i, w i ^ (b i).toNat

/-- Product weight, extended by zero to forbidden words. -/
def weight {N : ℕ} (w : Fin N → ℝ) (b : Fin N → Bool) : ℝ :=
  if Adm N b then monomial w b else 0

/-- The partition function sums over all legal words. -/
def partition {N : ℕ} (w : Fin N → ℝ) : ℝ := ∑ b, weight w b

/-- The normalized site-activity law. -/
def law {N : ℕ} (w : Fin N → ℝ) (b : Fin N → Bool) : ℝ :=
  weight w b / partition w

/-- Site means, extended by zero after the finite path. -/
def meansOf {N : ℕ} (w : Fin N → ℝ) (i : ℕ) : ℝ :=
  if h : i < N then ∑ b, law w b * if b ⟨i, h⟩ then 1 else 0 else 0

/-- The empty-word probability expressed through the local tables. -/
def emptyMass (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∏ i : Fin (n + 1), seam u i.val) / ∏ i : Fin n, (1 - u (i.val + 1))

private theorem pair_factor (u v : ℝ) (hr : 1 - u - v ≠ 0)
    (a b : Bool) (h : ¬(a = true ∧ b = true)) :
    pair u v a b = (1 - u - v) * (u / (1 - u - v)) ^ a.toNat *
      (v / (1 - u - v)) ^ b.toNat := by
  cases a <;> cases b <;> simp_all [pair]
  all_goals field_simp

private theorem site_factor (u : ℝ) (hu : 1 - u ≠ 0) (a : Bool) :
    site u a = (1 - u) * (u / (1 - u)) ^ a.toNat := by
  cases a <;> simp [site]
  field_simp

private theorem monomial_activity (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 2)) (b : Fin (n + 2) → Bool) :
    monomial (activity u n) b =
      ((∏ i : Fin (n + 1), (u i.val / seam u i.val) ^ (b i.castSucc).toNat) *
        (∏ i : Fin (n + 1), (u (i.val + 1) / seam u i.val) ^ (b i.succ).toNat)) /
        ∏ i : Fin n, (u (i.val + 1) / (1 - u (i.val + 1))) ^
          (b i.succ.castSucc).toNat := by
  have hne (i : Fin n) : u (i.val + 1) ≠ 0 :=
    ne_of_gt (hu.1 _ (by omega)).1
  have hr (i : Fin (n + 1)) : seam u i.val ≠ 0 :=
    ne_of_gt (hu.2 _ (by have := i.isLt; omega))
  have hs (i : Fin n) : 1 - u (i.val + 1) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hu.1 _ (by omega)).2)
  unfold monomial activity
  rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Fin.prod_univ_succ (fun i : Fin (n + 1) =>
    (u i.val / seam u i.val) ^ (b i.castSucc).toNat)]
  rw [Fin.prod_univ_castSucc (fun i : Fin (n + 1) =>
    (u (i.val + 1) / seam u i.val) ^ (b i.succ).toNat)]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
    Fin.castSucc_zero, Fin.succ_last, Fin.castSucc_succ]
  have hi (i : Fin n) :
      (u (i.val + 1) * (1 - u (i.val + 1)) /
          (seam u i.val * seam u (i.val + 1))) ^ (b i.succ.castSucc).toNat =
      ((u (i.val + 1) / seam u (i.val + 1)) ^ (b i.succ.castSucc).toNat *
        (u (i.val + 1) / seam u i.val) ^ (b i.succ.castSucc).toNat) /
        (u (i.val + 1) / (1 - u (i.val + 1))) ^ (b i.succ.castSucc).toNat := by
    cases hb : b i.succ.castSucc <;> simp only [Bool.toNat_false, Bool.toNat_true,
      pow_zero, pow_one, one_mul, div_self (one_ne_zero : (1 : ℝ) ≠ 0)]
    field_simp [hne i, hr i.castSucc, hr i.succ, hs i]
  simp only [Fin.castSucc_succ] at hi
  simp_rw [hi]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  ring

private theorem completion_factor (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 2)) (b : Fin (n + 2) → Bool) (hb : Adm (n + 2) b) :
    completion u n b = emptyMass u n * monomial (activity u n) b := by
  have hr (i : Fin (n + 1)) : seam u i.val ≠ 0 :=
    ne_of_gt (hu.2 _ (by have := i.isLt; omega))
  have hs (i : Fin n) : 1 - u (i.val + 1) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hu.1 _ (by omega)).2)
  have hp (i : Fin (n + 1)) :
      pair (u i.val) (u (i.val + 1)) (b i.castSucc) (b i.succ) =
        seam u i.val * (u i.val / seam u i.val) ^ (b i.castSucc).toNat *
          (u (i.val + 1) / seam u i.val) ^ (b i.succ).toNat := by
    apply pair_factor _ _ (hr i)
    have h := (adm_iff_no_adjacent_true _ b).mp hb i.castSucc i.succ rfl
    rcases h with h | h <;> simp [h]
  unfold completion
  simp_rw [hp, site_factor _ (hs _)]
  rw [monomial_activity u n hu]
  simp only [Finset.prod_mul_distrib, emptyMass]
  ring

private theorem activity_pos (u : ℕ → ℝ) (n : ℕ) (hu : Interior u (n + 2)) :
    ∀ i, 0 < activity u n i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact div_pos (hu.1 0 (by omega)).1 (hu.2 0 (by omega))
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [activity, Fin.cons_succ, Fin.snoc_last]
      exact div_pos (hu.1 (n + 1) (by omega)).1 (hu.2 n (by omega))
    · simp only [activity, Fin.cons_succ, Fin.snoc_castSucc]
      exact div_pos (mul_pos (hu.1 (k.val + 1) (by omega)).1
        (sub_pos.mpr (hu.1 (k.val + 1) (by omega)).2))
        (mul_pos (hu.2 k.val (by have := k.isLt; omega))
          (hu.2 (k.val + 1) (by have := k.isLt; omega)))

/-- The completion is precisely the product law, and its normalization is explicit. -/
theorem reconstructed_activity_law (u : ℕ → ℝ) (n : ℕ) (hu : Interior u (n + 2)) :
    (∀ i, 0 < activity u n i) ∧
    law (activity u n) = completion u n ∧
    partition (activity u n) =
      (∏ i : Fin n, (1 - u (i.val + 1))) / ∏ i : Fin (n + 1), seam u i.val ∧
    Means u (n + 1) (law (activity u n)) := by
  have hc := unique_markov_completion u n hu
  have he (b : Fin (n + 2) → Bool) :
      completion u n b = emptyMass u n * weight (activity u n) b := by
    by_cases hb : Adm (n + 2) b
    · simpa [weight, hb] using completion_factor u n hu b hb
    · rw [hc.1.2.2 b hb, weight, if_neg hb, mul_zero]
  have hz : emptyMass u n * partition (activity u n) = 1 := by
    rw [partition, Finset.mul_sum]
    simp_rw [← he]
    exact hc.1.2.1
  have hp : partition (activity u n) = (emptyMass u n)⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hz
  have hl : law (activity u n) = completion u n := by
    funext b
    rw [law, hp, div_inv_eq_mul, he]
    ring
  refine ⟨activity_pos u n hu, hl, ?_, ?_⟩
  · simpa [emptyMass, inv_div] using hp
  · rw [hl]
    exact hc.2.1

private theorem empty_legal (N : ℕ) : Adm N (fun _ => false) := by
  rw [adm_iff_no_adjacent_true]
  simp

private theorem singleton_legal {N : ℕ} (i : Fin N) :
    Adm N (fun j => decide (j = i)) := by
  rw [adm_iff_no_adjacent_true]
  intro j k hjk
  by_cases hj : j = i
  · right
    have hk : k ≠ i := by
      intro hk
      subst j
      subst k
      omega
    simp [hk]
  · left
    simp [hj]

private theorem weight_empty {N : ℕ} (w : Fin N → ℝ) :
    weight w (fun _ => false) = 1 := by
  simp [weight, empty_legal, monomial]

private theorem weight_singleton {N : ℕ} (w : Fin N → ℝ) (i : Fin N) :
    weight w (fun j => decide (j = i)) = w i := by
  rw [weight, if_pos (singleton_legal i)]
  unfold monomial
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private theorem weight_nonneg {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (b : Fin N → Bool) : 0 ≤ weight w b := by
  unfold weight monomial
  split_ifs
  · exact Finset.prod_nonneg (fun i _ => pow_nonneg (hw i).le _)
  · rfl

private theorem partition_pos {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, 0 < w i) :
    0 < partition w := by
  have h := Finset.single_le_sum (fun b _ => weight_nonneg w hw b)
    (Finset.mem_univ (fun _ => false))
  rw [weight_empty] at h
  exact lt_of_lt_of_le zero_lt_one h

private theorem law_legal (n : ℕ) (w : Fin (n + 2) → ℝ) (hw : ∀ i, 0 < w i) :
    LegalLaw (n + 1) (law w) := by
  refine ⟨fun b => div_nonneg (weight_nonneg w hw b) (partition_pos w hw).le, ?_, ?_⟩
  · simp only [law, ← Finset.sum_div]
    change partition w / partition w = 1
    exact div_self (partition_pos w hw).ne'
  · intro b hb
    simp [law, weight, hb]

private theorem law_pos {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (b : Fin N → Bool) (hb : Adm N b) : 0 < law w b := by
  apply div_pos _ (partition_pos w hw)
  simp only [weight, hb, ite_true, monomial]
  exact Finset.prod_pos (fun i _ => pow_pos (hw i) _)

private theorem log_law {N : ℕ} (w : Fin N → ℝ) (hw : ∀ i, 0 < w i)
    (b : Fin N → Bool) (hb : Adm N b) :
    Real.log (law w b) = (∑ i, (if b i then 1 else 0) * Real.log (w i)) -
      Real.log (partition w) := by
  rw [law, weight, if_pos hb, monomial,
    Real.log_div (ne_of_gt (Finset.prod_pos (fun i _ => pow_pos (hw i) _)))
      (partition_pos w hw).ne',
    Real.log_prod (fun i _ => ne_of_gt (pow_pos (hw i) _))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases b i <;> simp

private theorem log_moment (n : ℕ) (u : ℕ → ℝ)
    (v w : Fin (n + 2) → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hm : Means u (n + 1) (law v)) :
    (∑ b, law v b * Real.log (law w b)) =
      (∑ i : Fin (n + 2), u i.val * Real.log (w i)) - Real.log (partition w) := by
  have he (b : Fin (n + 2) → Bool) :
      law v b * Real.log (law w b) = law v b *
        ((∑ i, (if b i then 1 else 0) * Real.log (w i)) - Real.log (partition w)) := by
    by_cases hb : Adm (n + 2) b
    · rw [log_law w hw b hb]
    · simp [law, weight, hb]
  simp_rw [he, mul_sub, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  change ∀ i : Fin (n + 2), (∑ b, law v b * if b i then 1 else 0) = u i.val at hm
  simp_rw [← Finset.sum_mul, hm]
  rw [(law_legal n v hv).2.1, one_mul]

private theorem laws_equal_of_means (n : ℕ) (u : ℕ → ℝ)
    (v w : Fin (n + 2) → ℝ) (hv : ∀ i, 0 < v i) (hw : ∀ i, 0 < w i)
    (hmv : Means u (n + 1) (law v)) (hmw : Means u (n + 1) (law w)) :
    law v = law w := by
  let d (b : Fin (n + 2) → Bool) :=
    (law v b - law w b) * (Real.log (law v b) - Real.log (law w b))
  have hd (b : Fin (n + 2) → Bool) : 0 ≤ d b := by
    by_cases hb : Adm (n + 2) b
    · have hp := law_pos v hv b hb
      have hq := law_pos w hw b hb
      rcases le_total (law v b) (law w b) with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
          (sub_nonpos.mpr (Real.log_le_log hp h))
      · exact mul_nonneg (sub_nonneg.mpr h)
          (sub_nonneg.mpr (Real.log_le_log hq h))
    · simp [d, law, weight, hb]
  have hsum : (∑ b, d b) = 0 := by
    simp only [d, sub_mul, mul_sub, Finset.sum_sub_distrib]
    rw [log_moment n u v v hv hv hmv, log_moment n u v w hv hw hmv,
      log_moment n u w v hw hv hmw, log_moment n u w w hw hw hmw]
    ring
  have hdz := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hd b)).mp hsum
  funext b
  by_cases hb : Adm (n + 2) b
  · have he := hdz b (Finset.mem_univ b)
    rcases mul_eq_zero.mp he with h | h
    · exact sub_eq_zero.mp h
    · exact Real.log_injOn_pos (law_pos v hv b hb) (law_pos w hw b hb) (sub_eq_zero.mp h)
  · simp [law, weight, hb]

private theorem weights_equal_of_laws {N : ℕ} (v w : Fin N → ℝ)
    (hw : ∀ i, 0 < w i) (he : law v = law w) : v = w := by
  have hz := congrFun he (fun _ => false)
  simp only [law, weight_empty, one_div] at hz
  have hp : partition v = partition w := inv_injective hz
  funext i
  have hi := congrFun he (fun j => decide (j = i))
  simp only [law, weight_singleton, hp] at hi
  exact (div_left_inj' (partition_pos w hw).ne').mp hi

/-- Among positive activities, the prescribed interior means determine exactly one vector. -/
theorem activity_mean_correspondence (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 2)) (w : Fin (n + 2) → ℝ) (hw : ∀ i, 0 < w i) :
    Means u (n + 1) (law w) ↔ w = activity u n := by
  have h := reconstructed_activity_law u n hu
  constructor
  · intro hm
    exact weights_equal_of_laws w (activity u n) h.1
      (laws_equal_of_means n u w (activity u n) hw h.1 hm h.2.2.2)
  · rintro rfl
    exact h.2.2.2

/-- Every positive activity vector has strictly interior means. -/
theorem positive_activity_means (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hw : ∀ i, 0 < w i) :
    Interior (meansOf w) (n + 2) ∧ Means (meansOf w) (n + 1) (law w) := by
  have hl := law_legal n w hw
  have hm (i : Fin (n + 2)) :
      meansOf w i.val = ∑ b, law w b * if b i then 1 else 0 := by
    simp [meansOf, i.isLt]
  have he : 0 < law w (fun _ => false) := law_pos w hw _ (empty_legal _)
  have hbounds (i : Fin (n + 2)) : 0 < meansOf w i.val ∧ meansOf w i.val < 1 := by
    have hpos : 0 < ∑ b, law w b * if b i then 1 else 0 := by
      apply Finset.sum_pos'
      · intro b _
        apply mul_nonneg (hl.1 b)
        split_ifs <;> norm_num
      · refine ⟨(fun j => decide (j = i)), Finset.mem_univ _, ?_⟩
        simpa using law_pos w hw _ (singleton_legal i)
    have hfalse : 0 < ∑ b, law w b * if b i then 0 else 1 := by
      apply Finset.sum_pos'
      · intro b _
        apply mul_nonneg (hl.1 b)
        split_ifs <;> norm_num
      · exact ⟨(fun _ => false), Finset.mem_univ _, by simpa using he⟩
    have hsum : (∑ b, law w b * if b i then 1 else 0) +
        (∑ b, law w b * if b i then 0 else 1) = 1 := by
      calc
        _ = ∑ b, law w b := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro b _
          cases b i <;> simp
        _ = 1 := hl.2.1
    rw [hm]
    exact ⟨hpos, by linarith⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi
    exact hbounds ⟨i, hi⟩
  · intro i hi
    let I : Fin (n + 2) := ⟨i, by omega⟩
    let J : Fin (n + 2) := ⟨i + 1, hi⟩
    have hgap : 0 < ∑ b, law w b * if b I = false ∧ b J = false then 1 else 0 := by
      apply Finset.sum_pos'
      · intro b _
        apply mul_nonneg (hl.1 b)
        split_ifs <;> norm_num
      · exact ⟨(fun _ => false), Finset.mem_univ _, by simpa using he⟩
    have hsum :
        (∑ b, law w b * if b I = false ∧ b J = false then 1 else 0) +
        (∑ b, law w b * if b I then 1 else 0) +
        (∑ b, law w b * if b J then 1 else 0) = 1 := by
      calc
        _ = ∑ b, law w b := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro b _
          have hzero : b I = true → b J = true → law w b = 0 := by
            intro hbI hbJ
            apply hl.2.2 b
            intro hb
            have hh := (adm_iff_no_adjacent_true _ b).mp hb I J (by rfl)
            simp [hbI, hbJ] at hh
          cases hI : b I <;> cases hJ : b J <;> simp [hzero, hI, hJ]
        _ = 1 := hl.2.1
    rw [← hm I, ← hm J] at hsum
    change 0 < 1 - meansOf w I.val - meansOf w J.val
    linarith
  · intro i
    exact (hm i).symm

#print axioms reconstructed_activity_law
#print axioms activity_mean_correspondence
#print axioms positive_activity_means

end
end D5.S3.Combinatorics.Graph.LegalWords.ActivityMeanCorrespondence

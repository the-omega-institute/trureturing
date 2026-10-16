/- GID: D5/S3/Combinatorics/Graph/LegalWords/ActivityInnovations
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/ActivityInnovations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive path activities have orthogonal innovations with explicit variances. -/

import D5.S3.Combinatorics.Graph.LegalWords.InhomogeneousMarkovCompletion
import D5.S3.Divergence.GibbsEquality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LegalWords.ActivityInnovations

open scoped BigOperators
open D5.S1.Words.AdmissibleWords.AdmissibleCount
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (adm_iff_no_adjacent_true)
open InhomogeneousMarkovCompletion

noncomputable section

/-- The empty-empty remainder on the edge from i to i+1. -/
def seam (u : ℕ → ℝ) (i : ℕ) : ℝ := 1 - u i - u (i + 1)

/-- Activities reconstructed from the means, including both boundary cancellations. -/
private def activity (u : ℕ → ℝ) (n : ℕ) : Fin (n + 2) → ℝ :=
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
private def emptyMass (u : ℕ → ℝ) (n : ℕ) : ℝ :=
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
private theorem reconstructed_law (u : ℕ → ℝ) (n : ℕ) (hu : Interior u (n + 2)) :
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
  have hlv := law_legal n v hv
  have hlw := law_legal n w hw
  have hac (a b : Fin (n + 2) → ℝ) (hb : ∀ i, 0 < b i)
      (x : Fin (n + 2) → Bool) (hx : law b x = 0) : law a x = 0 := by
    by_cases hlegal : Adm (n + 2) x
    · exact False.elim ((ne_of_gt (law_pos b hb x hlegal)) hx)
    · simp [law, weight, hlegal]
  have hkl (a b : Fin (n + 2) → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
      D5.S3.Divergence.ClassicalDPI.klDivergence (law a) (law b) =
        (∑ x, law a x * Real.log (law a x)) -
          ∑ x, law a x * Real.log (law b x) := by
    unfold D5.S3.Divergence.ClassicalDPI.klDivergence
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : Adm (n + 2) x
    · rw [Real.log_div (law_pos a ha x hx).ne' (law_pos b hb x hx).ne']
      ring
    · simp [law, weight, hx]
  have hnonneg := D5.S3.Divergence.GrandmotherTheorem.kl_divergence_nonneg
    (law w) (law v) ⟨hlw.1, hlw.2.1⟩ ⟨hlv.1, hlv.2.1⟩ (hac w v hv)
  have hsymm : D5.S3.Divergence.ClassicalDPI.klDivergence (law v) (law w) +
      D5.S3.Divergence.ClassicalDPI.klDivergence (law w) (law v) = 0 := by
    rw [hkl v w hv hw, hkl w v hw hv,
      log_moment n u v v hv hv hmv, log_moment n u v w hv hw hmv,
      log_moment n u w w hw hw hmw, log_moment n u w v hw hv hmw]
    ring
  apply (D5.S3.Divergence.GibbsEquality.kl_divergence_eq_zero_iff
    (law v) (law w) ⟨hlv.1, hlv.2.1⟩ ⟨hlw.1, hlw.2.1⟩ (hac v w hw)).mp
  have hnonneg' := D5.S3.Divergence.GrandmotherTheorem.kl_divergence_nonneg
    (law v) (law w) ⟨hlv.1, hlv.2.1⟩ ⟨hlw.1, hlw.2.1⟩ (hac v w hw)
  linarith

/-- Every positive activity vector has strictly interior means. -/
private theorem law_interior (n : ℕ) (w : Fin (n + 2) → ℝ)
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

private theorem law_markov (n : ℕ) (w : Fin (n + 2) → ℝ)
    (hw : ∀ i, 0 < w i) (hu : Interior (meansOf w) (n + 2))
    (hm : Means (meansOf w) (n + 1) (law w)) :
    Markov (n + 1) (law w) := by
  have hr := reconstructed_law (meansOf w) n hu
  have he : law w = completion (meansOf w) n :=
    (laws_equal_of_means n (meansOf w) w (activity (meansOf w) n)
      hw hr.1 hm hr.2.2.2).trans hr.2.1
  rw [he]
  exact (unique_markov_completion (meansOf w) n hu).2.2.1


/-- The centered next bit after subtracting its linear prediction from the current bit. -/
def edgeResidual (u v : ℝ) (a b : Bool) : ℝ :=
  ((if b then 1 else 0) - v) + v / (1 - u) * ((if a then 1 else 0) - u)

/-- The first centered bit followed by the successive prediction residuals. -/
def innovation {N : ℕ} (u : ℕ → ℝ) (b : Fin (N + 1) → Bool) : Fin (N + 1) → ℝ :=
  Fin.cases ((if b 0 then 1 else 0) - u 0)
    (fun i => edgeResidual (u i.val) (u (i.val + 1)) (b i.castSucc) (b i.succ))

private theorem cylinder_expect (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ)
    (m : ℕ) (hm : m ≤ n) (F : (Fin (m + 1) → Bool) → ℝ) :
    (∑ v, cylinder n P m hm v * F v) =
      ∑ b, P b * F (initialSegment m hm b) := by
  unfold cylinder
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp [mul_ite]

private theorem extension_expect (n : ℕ) (P : (Fin (n + 1) → Bool) → ℝ)
    (K : ℕ → Bool → Bool → ℝ)
    (hrec : ∀ (m : ℕ) (hm : m < n) (v : Fin (m + 1) → Bool) (b : Bool),
      cylinder n P (m + 1) (by omega) (Fin.snoc v b) =
        cylinder n P m (by omega) v * K m (v (Fin.last m)) b)
    (m : ℕ) (hm : m < n) (F : (Fin (m + 1) → Bool) → ℝ)
    (G : Bool → Bool → ℝ) :
    (∑ b, P b * F (initialSegment m (by omega) b) *
      G (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩)) =
    ∑ v, cylinder n P m (by omega) v * F v *
      ∑ a : Bool, K m (v (Fin.last m)) a * G (v (Fin.last m)) a := by
  let H : (Fin (m + 2) → Bool) → ℝ := fun v =>
    F (Fin.init v) * G (v (Fin.last m).castSucc) (v (Fin.last (m + 1)))
  have hh := cylinder_expect n P (m + 1) (by omega) H
  have he : (∑ b, P b * F (initialSegment m (by omega) b) *
      G (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩)) =
      ∑ v, cylinder n P (m + 1) (by omega) v * H v := by
    rw [hh]
    apply Finset.sum_congr rfl
    intro b _
    change P b * F (initialSegment m (by omega) b) *
      G (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩) =
      P b * (F (initialSegment m (by omega) b) *
        G (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩))
    ring
  rw [he, ← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (m + 2) => Bool),
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  change (∑ a : Bool, cylinder n P (m + 1) (by omega) (Fin.snoc v a) * H (Fin.snoc v a)) = _
  simp only [hrec m hm, H, Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem kernel_occupied (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 1)) (P : (Fin (n + 1) → Bool) → ℝ)
    (hP : LegalLaw n P) (hmean : Means u n P)
    (K : ℕ → Bool → Bool → ℝ)
    (hrec : ∀ (m : ℕ) (hm : m < n) (v : Fin (m + 1) → Bool) (b : Bool),
      cylinder n P (m + 1) (by omega) (Fin.snoc v b) =
        cylinder n P m (by omega) v * K m (v (Fin.last m)) b)
    (m : ℕ) (hm : m < n) :
    K m true true = 0 ∧ K m false true = u (m + 1) / (1 - u m) := by
  let I : Fin (n + 1) := ⟨m, by omega⟩
  let J : Fin (n + 1) := ⟨m + 1, by omega⟩
  have hfirst : (∑ v, cylinder n P m (by omega) v *
      if v (Fin.last m) then 1 else 0) = u m := by
    rw [cylinder_expect]
    exact hmean I
  have hvac : (∑ v, cylinder n P m (by omega) v *
      if v (Fin.last m) then 0 else 1) = 1 - u m := by
    rw [cylinder_expect]
    have htotal : (∑ b, P b * if b I then 1 else 0) +
        (∑ b, P b * if b I then 0 else 1) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert hP.2.1 using 1
      apply Finset.sum_congr rfl
      intro b _
      cases b I <;> simp
    change (∑ b, P b * if b I then 0 else 1) = _
    rw [hmean I] at htotal
    linarith
  have hzero : (∑ b, P b * (if b I then 1 else 0) * (if b J then 1 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    by_cases hi : b I = true
    · by_cases hj : b J = true
      · have hb : ¬ Adm (n + 1) b := by
          intro ha
          have ha' := (adm_iff_no_adjacent_true _ b).mp ha I J (by rfl)
          simp [hi, hj] at ha'
        simp [hP.2.2 b hb]
      · simp [hj]
    · simp [hi]
  have h11 := extension_expect n P K hrec m hm (fun _ => 1)
    (fun a b => (if a then 1 else 0) * (if b then 1 else 0))
  simp only [mul_one, Fintype.sum_bool, ite_true, Bool.false_eq_true,
    ite_false, mul_zero, mul_one, add_zero] at h11
  have h11r : (∑ v, cylinder n P m (by omega) v *
      (K m (v (Fin.last m)) true * if v (Fin.last m) then 1 else 0)) =
      u m * K m true true := by
    rw [← hfirst, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    cases v (Fin.last m) <;> simp
  rw [h11r] at h11
  have hz : K m true true = 0 := by
    have he : u m * K m true true = 0 := h11.symm.trans (by simpa only [mul_assoc] using hzero)
    exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (hu.1 m (by omega)).1)
  refine ⟨hz, ?_⟩
  have hnext := extension_expect n P K hrec m hm (fun _ => 1)
    (fun _ b => if b then 1 else 0)
  simp only [mul_one, Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false, mul_zero,
    add_zero] at hnext
  have hr : (∑ v, cylinder n P m (by omega) v * K m (v (Fin.last m)) true) =
      (1 - u m) * K m false true := by
    rw [← hvac, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    cases v (Fin.last m) <;> simp [hz]
  rw [hr] at hnext
  have hmnext := hmean J
  change (∑ b, P b * if b J then 1 else 0) = _ at hnext
  rw [hmnext] at hnext
  exact (eq_div_iff (ne_of_gt (sub_pos.mpr (hu.1 m (by omega)).2))).2 (by linarith)

private theorem residual_row_zero (u v : ℝ) (hu : u < 1)
    (K : Bool → Bool → ℝ) (hrows : ∀ a, (∑ b : Bool, K a b) = 1)
    (h11 : K true true = 0) (h01 : K false true = v / (1 - u)) (a : Bool) :
    (∑ b : Bool, K a b * edgeResidual u v a b) = 0 := by
  have hden : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu)
  have ht := hrows true
  have hf := hrows false
  simp only [Fintype.sum_bool] at ht hf
  have h00 : K false false = 1 - v / (1 - u) := by rw [h01] at hf; linarith
  have h10 : K true false = 1 := by rw [h11] at ht; linarith
  cases a <;> simp only [Fintype.sum_bool, edgeResidual, h11, h01, h00, h10,
    Bool.false_eq_true, ite_false, ite_true, zero_mul, one_mul, zero_sub, zero_add]
  all_goals field_simp [hden]
  all_goals ring

private theorem past_residual_zero (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 1)) (P : (Fin (n + 1) → Bool) → ℝ)
    (hP : LegalLaw n P) (hmean : Means u n P) (hM : Markov n P)
    (m : ℕ) (hm : m < n) (F : (Fin (m + 1) → Bool) → ℝ) :
    (∑ b, P b * F (initialSegment m (by omega) b) *
      edgeResidual (u m) (u (m + 1)) (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩)) = 0 := by
  obtain ⟨K, _, hrows, hrec⟩ := hM
  rw [extension_expect n P K hrec m hm F]
  apply Finset.sum_eq_zero
  intro v _
  have hk := kernel_occupied u n hu P hP hmean K hrec m hm
  rw [residual_row_zero (u m) (u (m + 1)) (hu.1 m (by omega)).2
    (K m) (hrows m hm) hk.1 hk.2]
  exact mul_zero _


private theorem centered_variance (u : ℕ → ℝ) (n : ℕ)
    (P : (Fin (n + 1) → Bool) → ℝ) (hP : LegalLaw n P) (hmean : Means u n P)
    (i : Fin (n + 1)) :
    (∑ b, P b * ((if b i then 1 else 0) - u i.val) ^ 2) =
      u i.val * (1 - u i.val) := by
  calc
    _ = (1 - 2 * u i.val) * (∑ b, P b * if b i then 1 else 0) +
        u i.val ^ 2 * ∑ b, P b := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      cases b i <;> norm_num <;> ring
    _ = _ := by rw [hmean i, hP.2.1]; ring

private theorem edge_variance (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 1)) (P : (Fin (n + 1) → Bool) → ℝ)
    (hP : LegalLaw n P) (hmean : Means u n P) (hM : Markov n P)
    (m : ℕ) (hm : m < n) :
    (∑ b, P b * edgeResidual (u m) (u (m + 1))
      (b ⟨m, by omega⟩) (b ⟨m + 1, by omega⟩) ^ 2) =
      u (m + 1) * seam u m / (1 - u m) := by
  let I : Fin (n + 1) := ⟨m, by omega⟩
  let J : Fin (n + 1) := ⟨m + 1, by omega⟩
  let a : ℝ := u (m + 1) / (1 - u m)
  have hz := past_residual_zero u n hu P hP hmean hM m hm
    (fun v => (if v (Fin.last m) then 1 else 0) - u m)
  have hvI := centered_variance u n P hP hmean I
  have hvJ := centered_variance u n P hP hmean J
  have he : (∑ b, P b * edgeResidual (u m) (u (m + 1)) (b I) (b J) ^ 2) =
      (∑ b, P b * ((if b J then 1 else 0) - u (m + 1)) ^ 2) -
      a ^ 2 * (∑ b, P b * ((if b I then 1 else 0) - u m) ^ 2) +
      2 * a * (∑ b, P b * ((if b I then 1 else 0) - u m) *
        edgeResidual (u m) (u (m + 1)) (b I) (b J)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    dsimp [edgeResidual, a]
    ring
  change (∑ b, P b * ((if b I then 1 else 0) - u m) *
    edgeResidual (u m) (u (m + 1)) (b I) (b J)) = 0 at hz
  change (∑ b, P b * ((if b I then 1 else 0) - u m) ^ 2) = _ at hvI
  change (∑ b, P b * ((if b J then 1 else 0) - u (m + 1)) ^ 2) = _ at hvJ
  change (∑ b, P b * edgeResidual (u m) (u (m + 1)) (b I) (b J) ^ 2) = _
  rw [he, hvI, hvJ, hz]
  dsimp [I, J, a, seam]
  field_simp [ne_of_gt (sub_pos.mpr (hu.1 m (by omega)).2)]
  ring

private theorem innovation_prefix (u : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n)
    (b : Fin (n + 1) → Bool) (i : Fin (m + 1)) :
    innovation u (initialSegment m hm b) i =
      innovation u b ⟨i.val, by omega⟩ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

private theorem innovations_orthogonal (u : ℕ → ℝ) (n : ℕ)
    (hu : Interior u (n + 1)) (P : (Fin (n + 1) → Bool) → ℝ)
    (hP : LegalLaw n P) (hmean : Means u n P) (hM : Markov n P) :
    ∀ i j : Fin (n + 1), i ≠ j →
      (∑ b, P b * innovation u b i * innovation u b j) = 0 := by
  have ordered (i j : Fin (n + 1)) (hij : i < j) :
      (∑ b, P b * innovation u b i * innovation u b j) = 0 := by
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij))
    have hi : i.val < j.val + 1 := by exact hij
    let I : Fin (j.val + 1) := ⟨i.val, hi⟩
    have h := past_residual_zero u n hu P hP hmean hM j.val j.isLt
      (fun v => innovation u v I)
    simp only [innovation_prefix] at h
    exact h
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact ordered i j h
  · convert ordered j i h using 1
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- Positive activities give orthogonal successive residuals and their exact squared norms. -/
theorem orthogonal_innovations (n : ℕ) (w : Fin (n + 2) → ℝ) (hw : ∀ i, 0 < w i) :
    (∀ i j : Fin (n + 2), i ≠ j →
      (∑ b, law w b * innovation (meansOf w) b i * innovation (meansOf w) b j) = 0) ∧
    (∑ b, law w b * innovation (meansOf w) b 0 ^ 2) =
      meansOf w 0 * (1 - meansOf w 0) ∧
    (∀ i : Fin (n + 1),
      (∑ b, law w b * innovation (meansOf w) b i.succ ^ 2) =
        meansOf w (i.val + 1) * seam (meansOf w) i.val / (1 - meansOf w i.val)) := by
  have h := law_interior n w hw
  have hl := law_legal n w hw
  have hM := law_markov n w hw h.1 h.2
  refine ⟨innovations_orthogonal (meansOf w) (n + 1) h.1 (law w) hl h.2 hM, ?_, ?_⟩
  · exact centered_variance (meansOf w) (n + 1) (law w) hl h.2 0
  · intro i
    exact edge_variance (meansOf w) (n + 1) h.1 (law w) hl h.2 hM i.val i.isLt

#print axioms orthogonal_innovations

end
end D5.S3.Combinatorics.Graph.LegalWords.ActivityInnovations

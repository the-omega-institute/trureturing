/- GID: D5/S3/Analytic/Knapsack/IntegerRankCapacityDefect
   generality: G
   mirror-B: D5/B/S3/Analytic/Knapsack/IntegerRankCapacityDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Distinct integer ranks give defect-sensitive capacity and exact prefix slack. -/

import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

open scoped BigOperators

namespace D5.S3.Analytic.Knapsack.IntegerRankCapacityDefect

theorem integer_rank_capacity_defect (I : Finset ℕ) (r : ℕ) (A N : ℝ) (c : ℕ → ℝ)
    (hr : 0 < r) (hA : 0 ≤ A) (_hN : 0 ≤ N) (hpos : ∀ d ∈ I, r ≤ d)
    (hc : ∀ d ∈ I, 0 ≤ c d ∧ c d ≤ A * (d : ℝ))
    (hbudget : (∑ d ∈ I, c d) ≤ N) :
    let x := fun d : ℕ => c d / (d : ℝ)
    let J := ∑ d ∈ I, x d
    let B := ∑ d ∈ I, c d
    let D := ∑ d ∈ I, x d * (A - x d)
    let C := (2 * (r : ℝ) - 1) * A
    let H := ∑ d ∈ I, x d * (A * ((d : ℝ) - r) -
      ∑ i ∈ I.filter (fun i => i < d), x i)
    B = (∑ d ∈ I, (d : ℝ) * x d) ∧
      0 ≤ D ∧ J ^ 2 + C * J + D ≤ 2 * A * B ∧ 2 * A * B ≤ 2 * A * N ∧
      0 ≤ C ^ 2 + 8 * A * N - 4 * D ∧
      J ≤ (Real.sqrt (C ^ 2 + 8 * A * N - 4 * D) - C) / 2 ∧
      (Real.sqrt (C ^ 2 + 8 * A * N - 4 * D) - C) / 2 ≤
        (Real.sqrt (C ^ 2 + 8 * A * N) - C) / 2 ∧
      J ^ 2 + C * J + D + 2 * H = 2 * A * B ∧ 0 ≤ H ∧
      (∀ d ∈ I, A * ((d : ℝ) - r) - (∑ i ∈ I.filter (fun i => i < d), x i) =
        ∑ i ∈ Finset.Ico r d, (A - if i ∈ I then x i else 0)) ∧
      (∀ d ∈ I, 0 ≤ A * ((d : ℝ) - r) -
        (∑ i ∈ I.filter (fun i => i < d), x i)) ∧
      (0 < A → (H = 0 ↔ ∀ d ∈ I, 0 < x d →
        ∀ i ∈ Finset.Ico r d, i ∈ I ∧ x i = A)) ∧
      (A = 0 → H = 0) := by
  classical
  dsimp only
  let x := fun d : ℕ => c d / (d : ℝ)
  have hd (d : ℕ) (hdI : d ∈ I) : (0 : ℝ) < d := by
    exact_mod_cast hr.trans_le (hpos d hdI)
  have hx (d : ℕ) (hdI : d ∈ I) : 0 ≤ x d ∧ x d ≤ A :=
    ⟨div_nonneg (hc d hdI).1 (hd d hdI).le,
      (div_le_iff₀ (hd d hdI)).mpr (hc d hdI).2⟩
  have hoccupancy (S : Finset ℕ) (hposS : ∀ d ∈ S, r ≤ d)
      (hxS : ∀ d ∈ S, 0 ≤ x d ∧ x d ≤ A) :
      (∑ d ∈ S, x d) ^ 2 + (2 * (r : ℝ) - 1) * A * (∑ d ∈ S, x d) +
        (∑ d ∈ S, x d * (A - x d)) ≤ 2 * A * (∑ d ∈ S, (d : ℝ) * x d) := by
    induction S using Finset.induction_on_max with
    | empty => simp
    | insert a S hmax ih =>
      have haS : a ∉ S := fun ha => (lt_irrefl a) (hmax a ha)
      have ha : r ≤ a := hposS a (Finset.mem_insert_self _ _)
      have hposOld : ∀ d ∈ S, r ≤ d :=
        fun d hdS => hposS d (Finset.mem_insert_of_mem hdS)
      have hxOld : ∀ d ∈ S, 0 ≤ x d ∧ x d ≤ A :=
        fun d hdS => hxS d (Finset.mem_insert_of_mem hdS)
      have hxa := hxS a (Finset.mem_insert_self _ _)
      have hcard : S.card ≤ a - r := by
        have hsub : S ⊆ Finset.Ico r a := by
          intro d hdS
          exact Finset.mem_Ico.mpr ⟨hposOld d hdS, hmax d hdS⟩
        simpa only [Nat.card_Ico] using Finset.card_le_card hsub
      have hsum : (∑ d ∈ S, x d) ≤ ((a : ℝ) - r) * A := by
        calc
          _ ≤ ∑ _d ∈ S, A := Finset.sum_le_sum (fun d hdS => (hxOld d hdS).2)
          _ = (S.card : ℝ) * A := by simp
          _ ≤ ((a : ℝ) - r) * A := by
            apply mul_le_mul_of_nonneg_right _ hA
            have hcast : (S.card : ℝ) ≤ ((a - r : ℕ) : ℝ) := by exact_mod_cast hcard
            simpa only [Nat.cast_sub ha] using hcast
      have hcross := mul_le_mul_of_nonneg_right hsum hxa.1
      have hi := ih hposOld hxOld
      simp only [Finset.sum_insert haS]
      nlinarith only [hi, hcross]
  have hexact (S : Finset ℕ) :
      (∑ d ∈ S, x d) ^ 2 + (2 * (r : ℝ) - 1) * A * (∑ d ∈ S, x d) +
        (∑ d ∈ S, x d * (A - x d)) +
        2 * (∑ d ∈ S, x d * (A * ((d : ℝ) - r) -
          ∑ i ∈ S.filter (fun i => i < d), x i)) =
        2 * A * (∑ d ∈ S, (d : ℝ) * x d) := by
    induction S using Finset.induction_on_max with
    | empty => simp
    | insert a S hmax ih =>
      have haS : a ∉ S := fun ha => (lt_irrefl a) (hmax a ha)
      have hnew : (insert a S).filter (fun i => i < a) = S := by
        rw [Finset.filter_insert, if_neg (lt_irrefl a)]
        exact Finset.filter_true_of_mem hmax
      have hold : (∑ d ∈ S, x d * (A * ((d : ℝ) - r) -
          ∑ i ∈ (insert a S).filter (fun i => i < d), x i)) =
          ∑ d ∈ S, x d * (A * ((d : ℝ) - r) -
            ∑ i ∈ S.filter (fun i => i < d), x i) := by
        apply Finset.sum_congr rfl
        intro d hdS
        rw [Finset.filter_insert, if_neg (hmax d hdS).not_gt]
      simp only [Finset.sum_insert haS]
      rw [hnew, hold]
      nlinarith only [ih]
  have hprefix (d : ℕ) (hdI : d ∈ I) :
      A * ((d : ℝ) - r) - (∑ i ∈ I.filter (fun i => i < d), x i) =
        ∑ i ∈ Finset.Ico r d, (A - if i ∈ I then x i else 0) := by
    have hsub : I.filter (fun i => i < d) ⊆ Finset.Ico r d := by
      intro i hi
      obtain ⟨hiI, hid⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_Ico.mpr ⟨hpos i hiI, hid⟩
    have hsum : (∑ i ∈ Finset.Ico r d, if i ∈ I then x i else 0) =
        ∑ i ∈ I.filter (fun i => i < d), x i := by
      calc
        _ = ∑ i ∈ I.filter (fun i => i < d), if i ∈ I then x i else 0 := by
          symm
          apply Finset.sum_subset hsub
          intro i hi hnot
          apply if_neg
          intro hiI
          exact hnot (Finset.mem_filter.mpr ⟨hiI, (Finset.mem_Ico.mp hi).2⟩)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          exact if_pos (Finset.mem_filter.mp hi).1
    rw [Finset.sum_sub_distrib, hsum]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (hpos d hdI)]
    ring
  have hg (d : ℕ) (hdI : d ∈ I) :
      0 ≤ A * ((d : ℝ) - r) - (∑ i ∈ I.filter (fun i => i < d), x i) := by
    rw [hprefix d hdI]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs with hiI
    · exact sub_nonneg.mpr (hx i hiI).2
    · exact sub_nonneg.mpr hA
  have hterm (d : ℕ) (hdI : d ∈ I) : 0 ≤ x d *
      (A * ((d : ℝ) - r) - ∑ i ∈ I.filter (fun i => i < d), x i) :=
    mul_nonneg (hx d hdI).1 (hg d hdI)
  have hzero (hAstr : 0 < A) :
      (∑ d ∈ I, x d * (A * ((d : ℝ) - r) -
        ∑ i ∈ I.filter (fun i => i < d), x i)) = 0 ↔
      ∀ d ∈ I, 0 < x d → ∀ i ∈ Finset.Ico r d, i ∈ I ∧ x i = A := by
    rw [Finset.sum_eq_zero_iff_of_nonneg hterm]
    constructor
    · intro hall d hdI hxd i hi
      have hgap := (mul_eq_zero.mp (hall d hdI)).resolve_left hxd.ne'
      rw [hprefix d hdI] at hgap
      have hnonneg (j : ℕ) (hj : j ∈ Finset.Ico r d) :
          0 ≤ A - if j ∈ I then x j else 0 := by
        split_ifs with hjI
        · exact sub_nonneg.mpr (hx j hjI).2
        · exact sub_nonneg.mpr hA
      have hzI := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hgap i hi
      by_cases hiI : i ∈ I
      · simp only [if_pos hiI] at hzI
        exact ⟨hiI, by linarith only [hzI]⟩
      · simp only [if_neg hiI, sub_zero] at hzI
        exact False.elim (hAstr.ne' hzI)
    · intro hall d hdI
      by_cases hxd : x d = 0
      · rw [hxd, zero_mul]
      · have hxdpos : 0 < x d := lt_of_le_of_ne (hx d hdI).1 (Ne.symm hxd)
        have hgap : A * ((d : ℝ) - r) -
            (∑ i ∈ I.filter (fun i => i < d), x i) = 0 := by
          rw [hprefix d hdI]
          apply Finset.sum_eq_zero
          intro i hi
          obtain ⟨hiI, hxi⟩ := hall d hdI hxdpos i hi
          rw [if_pos hiI, hxi, sub_self]
        rw [hgap, mul_zero]
  have hmass : (∑ d ∈ I, (d : ℝ) * x d) = ∑ d ∈ I, c d := by
    apply Finset.sum_congr rfl
    intro d hdI
    exact mul_div_cancel₀ (c d) (hd d hdI).ne'
  have hD : 0 ≤ ∑ d ∈ I, x d * (A - x d) :=
    Finset.sum_nonneg (fun d hdI =>
      mul_nonneg (hx d hdI).1 (sub_nonneg.mpr (hx d hdI).2))
  have hraw := hoccupancy I hpos hx
  rw [hmass] at hraw
  have hbudget' := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 2 * A)
  have hfinal := hraw.trans hbudget'
  have hJ : 0 ≤ ∑ d ∈ I, x d := Finset.sum_nonneg (fun d hdI => (hx d hdI).1)
  have hC : 0 ≤ (2 * (r : ℝ) - 1) * A := by
    have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr
    exact mul_nonneg (by linarith only [hrr]) hA
  have hrad : 0 ≤ ((2 * (r : ℝ) - 1) * A) ^ 2 + 8 * A * N -
      4 * (∑ d ∈ I, x d * (A - x d)) := by
    nlinarith only [hfinal, sq_nonneg ((2 * (r : ℝ) - 1) * A),
      sq_nonneg (∑ d ∈ I, x d), mul_nonneg hC hJ]
  have hroot : (∑ d ∈ I, x d) ≤
      (Real.sqrt (((2 * (r : ℝ) - 1) * A) ^ 2 + 8 * A * N -
        4 * (∑ d ∈ I, x d * (A - x d))) - (2 * (r : ℝ) - 1) * A) / 2 := by
    have hsquare := Real.sq_sqrt hrad
    have hsqrt := Real.sqrt_nonneg (((2 * (r : ℝ) - 1) * A) ^ 2 + 8 * A * N -
      4 * (∑ d ∈ I, x d * (A - x d)))
    nlinarith only [hfinal, hJ, hC, hsquare, hsqrt]
  have hrootchain := Real.sqrt_le_sqrt
    (show ((2 * (r : ℝ) - 1) * A) ^ 2 + 8 * A * N -
      4 * (∑ d ∈ I, x d * (A - x d)) ≤
      ((2 * (r : ℝ) - 1) * A) ^ 2 + 8 * A * N by linarith only [hD])
  have hexactI := hexact I
  rw [hmass] at hexactI
  refine ⟨hmass.symm, hD, hraw, hbudget', hrad, hroot, by linarith only [hrootchain],
    hexactI, Finset.sum_nonneg hterm, hprefix, hg, hzero, ?_⟩
  intro hAzero
  apply Finset.sum_eq_zero
  intro d hdI
  have hxzero : x d = 0 := by
    have hxd := hx d hdI
    rw [hAzero] at hxd
    linarith only [hxd.1, hxd.2]
  dsimp only [x] at hxzero
  rw [hxzero, zero_mul]

#print axioms integer_rank_capacity_defect

end D5.S3.Analytic.Knapsack.IntegerRankCapacityDefect

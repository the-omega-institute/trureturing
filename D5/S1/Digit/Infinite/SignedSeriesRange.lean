/- GID: D5/S1/Digit/Infinite/SignedSeriesRange
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SignedSeriesRange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed golden series on legal infinite digits fills an interval with unique alternating endpoints. -/

import D5.S1.Digit.Infinite.SuccessorContinuity
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SignedSeriesRange

open D5.S1.Digit.Infinite.SuccessorContinuity
open scoped Topology

/-- The reciprocal of the golden ratio. -/
noncomputable def alpha : ℝ := Real.goldenRatio⁻¹

/-- The lower endpoint of the signed series interval. -/
noncomputable def a : ℝ := -alpha

/-- The upper endpoint of the signed series interval. -/
noncomputable def b : ℝ := alpha ^ 2

/-- The signed golden series, with digits indexed from low to high. -/
noncomputable def signedValue (x : LegalDigits) : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) * (if x.val j then 1 else 0)

/-- The alternating stream with ones at the even positions. -/
def u : LegalDigits := ⟨fun i => decide (i % 2 = 0), by
  intro j
  simp only [decide_eq_true_eq]
  omega⟩

/-- The alternating stream with ones at the odd positions. -/
def v : LegalDigits := ⟨fun i => decide (i % 2 = 1), by
  intro j
  simp only [decide_eq_true_eq]
  omega⟩

/-- The signed series fills the closed interval, and each endpoint has its unique
alternating stream. -/
theorem signed_series_range : Set.range signedValue = Set.Icc a b ∧
    (∀ x : LegalDigits, signedValue x = a ↔ x = u) ∧
    (∀ x : LegalDigits, signedValue x = b ↔ x = v) := by
  classical
  have hp : 0 < alpha := inv_pos.mpr Real.goldenRatio_pos
  have hlt : alpha < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have ha : alpha ^ 2 + alpha = 1 := by
    dsimp [alpha]
    rw [Real.inv_goldenRatio]
    nlinarith [Real.goldenConj_sq]
  have hsq : alpha ^ 2 < 1 := by nlinarith
  have hone : 1 - alpha ^ 2 = alpha := by linarith
  let term (x : LegalDigits) (j : ℕ) : ℝ :=
    (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) * (if x.val j then 1 else 0)
  have summable_term (x : LegalDigits) : Summable (term x) := by
    apply ((summable_geometric_of_lt_one hp.le hlt).mul_right (alpha ^ 2)).of_norm_bounded
    intro j
    dsimp [term]
    rw [abs_mul, abs_mul, abs_pow, abs_pow]
    simp only [abs_neg, abs_one, one_pow, one_mul, abs_of_pos hp]
    cases x.val j <;> simp [pow_add, mul_nonneg (pow_nonneg hp.le j) (sq_nonneg alpha)]
  have even_term (x : LegalDigits) (k : ℕ) :
      term x (2 * k) = -(alpha ^ 2) ^ k * alpha ^ 2 * (if x.val (2 * k) then 1 else 0) := by
    simp [term, pow_add, pow_mul]
  have odd_term (x : LegalDigits) (k : ℕ) :
      term x (2 * k + 1) = (alpha ^ 2) ^ k * alpha ^ 3 *
        (if x.val (2 * k + 1) then 1 else 0) := by
    simp [term, pow_add, pow_mul]
    ring
  have value_u : signedValue u = a := by
    have he : HasSum (fun k => term u (2 * k)) (-alpha) := by
      convert! (hasSum_geometric_of_lt_one (sq_nonneg alpha) hsq).mul_left (-alpha ^ 2) using 1
      · funext k
        simp [even_term, u]
        ring
      · rw [hone]
        field_simp [hp.ne']
    have ho : HasSum (fun k => term u (2 * k + 1)) 0 := by
      simp [odd_term, u]
    simpa [a, signedValue, term] using (he.even_add_odd ho).tsum_eq
  have value_v : signedValue v = b := by
    have he : HasSum (fun k => term v (2 * k)) 0 := by
      simp [even_term, v]
    have ho : HasSum (fun k => term v (2 * k + 1)) (alpha ^ 2) := by
      convert! (hasSum_geometric_of_lt_one (sq_nonneg alpha) hsq).mul_left (alpha ^ 3) using 1
      · funext k
        simp [odd_term, v]
        ring
      · rw [hone]
        field_simp [hp.ne']
    simpa [b, signedValue, term] using (he.even_add_odd ho).tsum_eq
  have comparison (x : LegalDigits) (j : ℕ) :
      term u j ≤ term x j ∧ term x j ≤ term v j := by
    have hj : j = 2 * (j / 2) ∨ j = 2 * (j / 2) + 1 := by omega
    rcases hj with hj | hj
    · rw [hj, even_term, even_term, even_term]
      simp only [u, v, Nat.mul_mod_right, decide_true, ↓reduceIte, mul_one]
      have hnonneg : 0 ≤ (alpha ^ 2) ^ (j / 2) * alpha ^ 2 :=
        mul_nonneg (pow_nonneg (sq_nonneg alpha) _) (sq_nonneg alpha)
      cases x.val (2 * (j / 2)) <;> simp <;> nlinarith
    · rw [hj, odd_term, odd_term, odd_term]
      simp only [u, v, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.one_mod,
        decide_true, ↓reduceIte, mul_one]
      have hnonneg : 0 ≤ (alpha ^ 2) ^ (j / 2) * alpha ^ 3 :=
        mul_nonneg (pow_nonneg (sq_nonneg alpha) _) (pow_nonneg hp.le _)
      cases x.val (2 * (j / 2) + 1) <;> simp <;> nlinarith
  have bounds (x : LegalDigits) : a ≤ signedValue x ∧ signedValue x ≤ b := by
    rw [← value_u, ← value_v]
    exact ⟨(summable_term u).tsum_le_tsum (fun j => (comparison x j).1) (summable_term x),
      (summable_term x).tsum_le_tsum (fun j => (comparison x j).2) (summable_term v)⟩
  have rigid (x y : LegalDigits) (horder : ∀ j, term x j ≤ term y j)
      (heq : signedValue x = signedValue y) : x = y := by
    apply Subtype.ext
    funext j
    have ht : term x j = term y j := by
      by_contra hne
      have hs := (summable_term x).tsum_lt_tsum horder
        (lt_of_le_of_ne (horder j) hne) (summable_term y)
      change signedValue x < signedValue y at hs
      exact (ne_of_lt hs) heq
    have hn : (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hp.ne')
    have hd := mul_left_cancel₀ hn ht
    cases hx : x.val j <;> cases hy : y.val j <;> simp_all [term]
  refine ⟨?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro t ⟨x, rfl⟩
      exact bounds x
    · intro t ht
      have hc : alpha ^ 3 + alpha ^ 2 = alpha := by
        nlinarith [congrArg (fun z : ℝ => alpha * z) ha]
      have hfour : alpha ^ 4 + alpha ^ 3 = alpha ^ 2 := by
        nlinarith [congrArg (fun z : ℝ => alpha ^ 2 * z) ha]
      -- At the common endpoint, choose the branch whose first digit is zero.
      let q : ℝ := -(alpha ^ 3)
      let step (z : ℝ) : ℝ := if z < q then -(z + alpha ^ 2) / alpha else -z / alpha
      have step_interval (z : ℝ) (hz : z ∈ Set.Icc a b) :
          step z ∈ Set.Icc a b ∧ (z < q → q ≤ step z) := by
        rcases hz with ⟨hzl, hzu⟩
        change -alpha ≤ z at hzl
        change z ≤ alpha ^ 2 at hzu
        by_cases h : z < q
        · simp only [step, if_pos h]
          change (-alpha ≤ -(z + alpha ^ 2) / alpha ∧
            -(z + alpha ^ 2) / alpha ≤ alpha ^ 2) ∧
            (z < q → q ≤ -(z + alpha ^ 2) / alpha)
          dsimp [q] at h ⊢
          constructor
          · constructor
            · apply (le_div_iff₀ hp).mpr
              nlinarith [pow_pos hp 3]
            · apply (div_le_iff₀ hp).mpr
              nlinarith
          · intro _
            apply (le_div_iff₀ hp).mpr
            nlinarith
        · simp only [step, if_neg h]
          change (-alpha ≤ -z / alpha ∧ -z / alpha ≤ alpha ^ 2) ∧
            (z < q → q ≤ -z / alpha)
          constructor
          · constructor
            · apply (le_div_iff₀ hp).mpr
              nlinarith
            · apply (div_le_iff₀ hp).mpr
              dsimp [q] at h
              nlinarith
          · exact fun h' => (h h').elim
      let residual : ℕ → ℝ := Nat.rec t (fun _ z => step z)
      have residual_step (n : ℕ) : residual (n + 1) = step (residual n) := rfl
      have residual_mem (n : ℕ) : residual n ∈ Set.Icc a b := by
        induction n with
        | zero => exact ht
        | succ n ih => exact (step_interval (residual n) ih).1
      -- A digit equal to one forces the next residual into the zero branch.
      let x : LegalDigits := by
        classical
        exact ⟨fun n => decide (residual n < q), by
          intro n
          simp only [decide_eq_true_eq]
          rintro ⟨hn, hn1⟩
          exact (not_lt_of_ge ((step_interval (residual n) (residual_mem n)).2 hn)) hn1⟩
      have recurrence (n : ℕ) : residual n =
          -alpha ^ 2 * (if x.val n then 1 else 0) + (-alpha) * residual (n + 1) := by
        rw [residual_step]
        simp only [x, decide_eq_true_eq]
        rcases lt_or_ge (residual n) q with h | h
        · simp [step, h]
          field_simp [hp.ne']
          ring
        · simp [step, not_lt.mpr h]
          field_simp [hp.ne']
      have coefficient (n : ℕ) : term x n =
          (-alpha) ^ n * (-alpha ^ 2) * (if x.val n then 1 else 0) := by
        rw [neg_pow alpha n]
        simp only [term, pow_add, pow_one]
        ring
      have partial_sum (n : ℕ) :
          (∑ j ∈ Finset.range n, term x j) = t - (-alpha) ^ n * residual n := by
        induction n with
        | zero => simp [residual]
        | succ n ih =>
          rw [Finset.sum_range_succ, ih, coefficient, pow_succ (-alpha) n]
          have hn := recurrence n
          nlinarith [congrArg (fun z : ℝ => (-alpha) ^ n * z) hn]
      have residual_bound (n : ℕ) : |residual n| ≤ 1 := by
        have hn := residual_mem n
        change -alpha ≤ residual n ∧ residual n ≤ alpha ^ 2 at hn
        exact abs_le.mpr ⟨by linarith [hn.1], by linarith [hn.2]⟩
      have remainder_zero : Filter.Tendsto (fun n => (-alpha) ^ n * residual n)
          Filter.atTop (𝓝 0) := by
        apply squeeze_zero_norm (fun n => ?_)
          (tendsto_pow_atTop_nhds_zero_of_lt_one hp.le hlt)
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos hp]
        exact mul_le_of_le_one_right (pow_nonneg hp.le n) (residual_bound n)
      have value_x : signedValue x = t := by
        apply tendsto_nhds_unique (summable_term x).hasSum.tendsto_sum_nat
        have h : Filter.Tendsto (fun n => t - (-alpha) ^ n * residual n)
            Filter.atTop (𝓝 (t - 0)) := tendsto_const_nhds.sub remainder_zero
        simpa only [sub_zero, ← partial_sum] using h
      exact ⟨x, value_x⟩
  · intro x
    exact ⟨fun h => (rigid u x (fun j => (comparison x j).1) (value_u.trans h.symm)).symm,
      fun h => h ▸ value_u⟩
  · intro x
    exact ⟨fun h => rigid x v (fun j => (comparison x j).2) (h.trans value_v.symm),
      fun h => h ▸ value_v⟩

end D5.S1.Digit.Infinite.SignedSeriesRange

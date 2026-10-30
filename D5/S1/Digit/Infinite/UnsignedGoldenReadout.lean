/- GID: D5/S1/Digit/Infinite/UnsignedGoldenReadout
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/UnsignedGoldenReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unsigned golden readout: interval range, continuity and prefix control. -/

import D5.S1.Digit.Infinite.SignedSeriesRange
import D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
import D5.S1.Deficit.Displacement.GoldenInverseRecurrence
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.UnsignedGoldenReadout

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.SignedSeriesRange (u v)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel (bitShift)
open D5.S1.Deficit.Displacement.GoldenInverseRecurrence
open scoped Topology

local notation "r" => (Real.goldenRatio⁻¹ : ℝ)

/-- The unsigned readout, with position zero having weight inverse golden ratio. -/
noncomputable def U (x : LegalDigits) : ℝ :=
  ∑' k : ℕ, (if x.val k then 1 else 0) * r ^ (k + 1)

/-- The name with every digit zero. -/
def zeroName : LegalDigits := ⟨fun _ => false, by simp⟩

/-- The name whose only occupied digit is position zero. -/
def singleName : LegalDigits := ⟨fun k => decide (k = 0), by
  intro j
  simp only [decide_eq_true_eq]
  omega⟩

private noncomputable def term (x : LegalDigits) (k : ℕ) : ℝ :=
  (if x.val k then 1 else 0) * r ^ (k + 1)

private theorem ratio_pos : 0 < r := inv_pos.mpr Real.goldenRatio_pos

private theorem ratio_lt_one : r < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

private theorem term_summable (x : LegalDigits) : Summable (term x) := by
  apply ((summable_geometric_of_lt_one ratio_pos.le ratio_lt_one).mul_right r).of_norm_bounded
  intro k
  dsimp [term]
  rw [abs_mul, abs_pow, abs_of_pos ratio_pos]
  cases x.val k
  · simp only [Bool.false_eq_true, ↓reduceIte, abs_zero, zero_mul]
    exact mul_nonneg (pow_nonneg ratio_pos.le k) ratio_pos.le
  · simp only [↓reduceIte, abs_one, one_mul, pow_succ, le_refl]

private theorem value_bounds (x : LegalDigits) : U x ∈ Set.Icc (0 : ℝ) 1 := by
  have he : Summable (fun k => term x (2 * k)) :=
    (term_summable x).comp_injective (by intro a b h; change 2 * a = 2 * b at h; omega)
  have ho : Summable (fun k => term x (2 * k + 1)) :=
    (term_summable x).comp_injective (by intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)
  have hsq : r ^ 2 < 1 := by nlinarith [inv_goldenRatio_sq_add_inv_goldenRatio, ratio_pos]
  have hg : HasSum (fun k : ℕ => (r ^ 2) ^ k * r) 1 := by
    convert! (hasSum_geometric_of_lt_one (sq_nonneg r) hsq).mul_right r using 1
    rw [show 1 - r ^ 2 = r by linarith [inv_goldenRatio_sq_add_inv_goldenRatio]]
    rw [inv_mul_cancel₀ ratio_pos.ne']
  have pairs (k : ℕ) : term x (2 * k) + term x (2 * k + 1) ≤ (r ^ 2) ^ k * r := by
    have hc := x.property (2 * k)
    have hn := pow_nonneg ratio_pos.le (2 * k + 1)
    have hs : r ^ (2 * k + 2) ≤ r ^ (2 * k + 1) := by
      rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, pow_succ]
      exact mul_le_of_le_one_right hn ratio_lt_one.le
    have hp : (r ^ 2) ^ k * r = r ^ (2 * k + 1) := by
      rw [← pow_mul, pow_succ]
    rw [hp]
    cases h0 : x.val (2 * k) <;> cases h1 : x.val (2 * k + 1) <;>
      simp_all [term]
  constructor
  · change 0 ≤ ∑' k, term x k
    exact tsum_nonneg (fun k => by dsimp [term]; positivity)
  · calc
      U x = (∑' k, term x (2 * k)) + ∑' k, term x (2 * k + 1) :=
        (he.hasSum.even_add_odd ho.hasSum).tsum_eq
      _ = ∑' k, (term x (2 * k) + term x (2 * k + 1)) := (he.tsum_add ho).symm
      _ ≤ ∑' k, (r ^ 2) ^ k * r := (he.add ho).tsum_le_tsum pairs hg.summable
      _ = 1 := hg.tsum_eq

private theorem value_split (x : LegalDigits) (n : ℕ) :
    U x = (∑ k ∈ Finset.range n, term x k) + r ^ n * U (bitShift x n) := by
  have ht : (∑' k, term x (k + n)) = r ^ n * U (bitShift x n) := by
    rw [U, ← tsum_mul_left]
    apply tsum_congr
    intro k
    dsimp [term, bitShift]
    rw [show k + n + 1 = n + (k + 1) by omega, pow_add]
    ac_rfl
  exact ((term_summable x).sum_add_tsum_nat_add n).symm.trans (congrArg _ ht)

private theorem value_onto (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ∃ x, U x = t := by
  classical
  let step (z : ℝ) : ℝ := if r < z then (z - r) / r else z / r
  have step_interval (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
      step z ∈ Set.Icc (0 : ℝ) 1 ∧ (r < z → step z ≤ r) := by
    by_cases h : r < z
    · simp only [step, if_pos h]
      constructor
      · constructor
        · exact div_nonneg (by linarith) ratio_pos.le
        · apply (div_le_iff₀ ratio_pos).mpr
          nlinarith [inv_goldenRatio_sq_add_inv_goldenRatio, ratio_pos, hz.2]
      · intro _
        apply (div_le_iff₀ ratio_pos).mpr
        nlinarith [inv_goldenRatio_sq_add_inv_goldenRatio, hz.2]
    · simp only [step, if_neg h]
      refine ⟨⟨div_nonneg hz.1 ratio_pos.le, ?_⟩, fun hh => (h hh).elim⟩
      exact (div_le_one ratio_pos).mpr (le_of_not_gt h)
  let residual : ℕ → ℝ := Nat.rec t (fun _ z => step z)
  have residual_mem (n : ℕ) : residual n ∈ Set.Icc (0 : ℝ) 1 := by
    induction n with
    | zero => exact ht
    | succ n ih => exact (step_interval (residual n) ih).1
  let x : LegalDigits := ⟨fun n : ℕ => @decide (r < residual n) (Classical.propDecidable _), by
    intro n
    simp only [decide_eq_true_eq]
    rintro ⟨hn, hn1⟩
    exact (not_lt_of_ge ((step_interval (residual n) (residual_mem n)).2 hn)) hn1⟩
  have recurrence (n : ℕ) : residual n =
      r * (if x.val n then (1 : ℝ) else 0) + r * residual (n + 1) := by
    change residual n = r * (if x.val n then (1 : ℝ) else 0) +
      r * step (residual n)
    rcases lt_or_ge r (residual n) with h | h
    · have hd : x.val n = true :=
        @decide_eq_true (r < residual n) (Classical.propDecidable _) h
      rw [hd]
      simp only [↓reduceIte, step, if_pos h, mul_one]
      field_simp [ratio_pos.ne']
      ring
    · have hd : x.val n = false :=
        @decide_eq_false (r < residual n) (Classical.propDecidable _) (not_lt.mpr h)
      rw [hd]
      simp only [Bool.false_eq_true, ↓reduceIte, step, if_neg (not_lt.mpr h),
        mul_zero, zero_add]
      field_simp [ratio_pos.ne']
  have partial_sum (n : ℕ) :
      (∑ k ∈ Finset.range n, term x k) = t - r ^ n * residual n := by
    induction n with
    | zero => simp [residual]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [term]
      rw [pow_succ]
      nlinarith [congrArg (fun z : ℝ => r ^ n * z) (recurrence n)]
  have remainder_zero : Filter.Tendsto (fun n => r ^ n * residual n)
      Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one ratio_pos.le ratio_lt_one)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos ratio_pos,
      abs_of_nonneg (residual_mem n).1]
    exact mul_le_of_le_one_right (pow_nonneg ratio_pos.le n) (residual_mem n).2
  refine ⟨x, ?_⟩
  apply tendsto_nhds_unique (term_summable x).hasSum.tendsto_sum_nat
  have h := tendsto_const_nhds (x := t) |>.sub remainder_zero
  simpa only [sub_zero, ← partial_sum] using h

/-- The readout is a continuous surjection with the full prefix estimate, endpoint
names, and two different legal names of the inverse golden ratio. -/
theorem unsigned_golden_readout :
    (∀ x : LegalDigits, Summable (fun k : ℕ =>
      (if x.val k then (1 : ℝ) else 0) * r ^ (k + 1))) ∧
    Set.range U = Set.Icc (0 : ℝ) 1 ∧
    Continuous U ∧
    (∀ (n : ℕ) (x y : LegalDigits),
      (∀ k < n, x.val k = y.val k) → |U x - U y| ≤ r ^ n) ∧
    U zeroName = 0 ∧ U u = 1 ∧
    singleName ≠ v ∧ U singleName = r ∧ U v = r := by
  have hzero : U zeroName = 0 := by simp [U, zeroName]
  have hsingle : U singleName = r := by
    rw [U, tsum_eq_single 0]
    · simp [singleName]
    · intro k hk
      simp [singleName, hk]
  have hsq : r ^ 2 < 1 := by nlinarith [inv_goldenRatio_sq_add_inv_goldenRatio, ratio_pos]
  have hgeom : HasSum (fun k : ℕ => (r ^ 2) ^ k) (1 / r) := by
    convert! hasSum_geometric_of_lt_one (sq_nonneg r) hsq using 1
    rw [show 1 - r ^ 2 = r by linarith [inv_goldenRatio_sq_add_inv_goldenRatio]]
    exact one_div r
  have hu : U u = 1 := by
    have he : HasSum (fun k => term u (2 * k)) 1 := by
      convert! hgeom.mul_right r using 1
      · funext k
        simp [term, u, pow_add, pow_mul]
      · rw [one_div, inv_mul_cancel₀ ratio_pos.ne']
    have ho : HasSum (fun k => term u (2 * k + 1)) 0 := by simp [term, u]
    simpa only [add_zero, U, term] using (he.even_add_odd ho).tsum_eq
  have hv : U v = r := by
    have he : HasSum (fun k => term v (2 * k)) 0 := by simp [term, v]
    have ho : HasSum (fun k => term v (2 * k + 1)) r := by
      convert! hgeom.mul_right (r ^ 2) using 1
      · funext k
        simp [term, v, pow_add, pow_mul, pow_two, mul_assoc]
      · field_simp [ratio_pos.ne']
    simpa only [zero_add, U, term] using (he.even_add_odd ho).tsum_eq
  refine ⟨term_summable, ?_, ?_, ?_, hzero, hu, ?_, hsingle, hv⟩
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact value_bounds x
    · exact fun t ht => value_onto t ht
  · apply continuous_tsum
    · intro k
      apply Continuous.mul _ continuous_const
      exact (continuous_of_discreteTopology :
        Continuous (fun b : Bool => if b then (1 : ℝ) else 0)).comp
        ((continuous_apply k).comp continuous_subtype_val)
    · exact (summable_geometric_of_lt_one ratio_pos.le ratio_lt_one).mul_right r
    · intro k x
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos ratio_pos]
      cases x.val k
      · simp only [Bool.false_eq_true, ↓reduceIte, abs_zero, zero_mul]
        exact mul_nonneg (pow_nonneg ratio_pos.le k) ratio_pos.le
      · simp only [↓reduceIte, abs_one, one_mul, pow_succ, le_refl]
  · intro n x y hxy
    have hp : (∑ k ∈ Finset.range n, term x k) = ∑ k ∈ Finset.range n, term y k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [term, hxy k (Finset.mem_range.mp hk)]
    rw [value_split x n, value_split y n, hp]
    have hx := value_bounds (bitShift x n)
    have hy := value_bounds (bitShift y n)
    have hn := pow_nonneg ratio_pos.le n
    apply abs_le.mpr
    constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
  · intro h
    have hh := congrArg (fun x : LegalDigits => x.val 0) h
    simp [singleName, v] at hh

#print axioms unsigned_golden_readout

end D5.S1.Digit.Infinite.UnsignedGoldenReadout

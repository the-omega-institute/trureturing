/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/PhiSeries
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First 32 terms and a uniform tail bound for the regularized exponential quotient. -/

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Series enclosures for the regularized exponential quotient and its first two derivatives. -/

open scoped BigOperators Topology

set_option autoImplicit false

noncomputable section

namespace RefinedBMV.FourSpectrumLift

/-- The regularized exponential ratio appearing in the zero-center denominator. -/
def phi (x : ℝ) : ℝ :=
  if x = 0 then 1 else (Real.exp x - 1) / x

theorem hasDerivAt_phi {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt phi ((Real.exp x * (x - 1) + 1) / x ^ 2) x := by
  have h := ((Real.hasDerivAt_exp x).sub_const 1).fun_div (hasDerivAt_id' x) hx
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · change (Real.exp x * x - (Real.exp x - 1) * 1) / x ^ 2 = _
    congr 1
    ring
  · filter_upwards [eventually_ne_nhds hx] with y hy
    simp [phi, hy]

theorem hasDerivAt_deriv_phi {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (deriv phi) ((Real.exp x * (x ^ 2 - 2 * x + 2) - 2) / x ^ 3) x := by
  have hnum : HasDerivAt (fun y : ℝ => Real.exp y * (y - 1) + 1) (Real.exp x * x) x := by
    have h := ((Real.hasDerivAt_exp x).fun_mul ((hasDerivAt_id' x).sub_const 1)).add_const 1
    refine h.congr_deriv ?_
    change Real.exp x * (x - 1) + Real.exp x * 1 = Real.exp x * x
    ring
  have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_id' x).fun_pow 2
  have h := hnum.fun_div hden (pow_ne_zero 2 hx)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · change (Real.exp x * x * x ^ 2 - (Real.exp x * (x - 1) + 1) * (2 * x)) /
        (x ^ 2) ^ 2 = _
    field_simp [hx] <;> ring
  · filter_upwards [eventually_ne_nhds hx] with y hy
    exact (hasDerivAt_phi hy).deriv

/-- The coefficient including the monomial for derivative order `k`. -/
def phiSeriesTerm (x : ℝ) (k j : ℕ) : ℝ :=
  x ^ j / ((j.factorial : ℝ) * ((j : ℝ) + (k : ℝ) + 1))

/-- The 32 terms used in the near-zero box cover. -/
def phiSeriesPartial (x : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 32, phiSeriesTerm x k j

private theorem cast_factorial_succ (j : ℕ) :
    ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

private theorem hasSum_exp_shift (x : ℝ) (hx : x ≠ 0) (m : ℕ) :
    HasSum (fun j : ℕ => x ^ j / ((j + m).factorial : ℝ))
      ((Real.exp x - ∑ i ∈ Finset.range m, x ^ i / (i.factorial : ℝ)) / x ^ m) := by
  have hexp : HasSum (fun j : ℕ => x ^ j / (j.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have hshift := (hasSum_nat_add_iff' m (f := fun j => x ^ j / (j.factorial : ℝ))
    (g := Real.exp x)).2 hexp
  refine (hshift.div_const (x ^ m)).congr_fun ?_
  intro j
  rw [pow_add, mul_div_right_comm (x ^ j) (x ^ m), mul_div_cancel_right₀ _ (pow_ne_zero m hx)]

/-- The positive series for the ratio and its first two derivatives. -/
theorem hasSum_phiSeries {x : ℝ} (hx : x ≠ 0) :
    HasSum (phiSeriesTerm x 0) (phi x) ∧
      HasSum (phiSeriesTerm x 1) (deriv phi x) ∧
      HasSum (phiSeriesTerm x 2) (deriv (deriv phi) x) := by
  have hp₁ : (∑ i ∈ Finset.range 1, x ^ i / (i.factorial : ℝ)) = 1 := by
    norm_num [Finset.sum_range_succ]
  have hp₂ : (∑ i ∈ Finset.range 2, x ^ i / (i.factorial : ℝ)) = 1 + x := by
    norm_num [Finset.sum_range_succ]
  have hp₃ : (∑ i ∈ Finset.range 3, x ^ i / (i.factorial : ℝ)) = 1 + x + x ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, add_assoc]
  have h₁ := hasSum_exp_shift x hx 1
  have h₂ := hasSum_exp_shift x hx 2
  have h₃ := hasSum_exp_shift x hx 3
  rw [hp₁, pow_one] at h₁
  rw [hp₂] at h₂
  rw [hp₃] at h₃
  -- After normalizing the three tails by x, x², and x³, the numerator
  -- combinations become h₁, h₁ - h₂, and h₁ - 2h₂ + 2h₃.
  refine ⟨?_, ?_, ?_⟩
  · rw [phi, ite_eq_right hx]
    refine h₁.congr_fun fun j => ?_
    simp [phiSeriesTerm, cast_factorial_succ, mul_comm]
  · have hvalue : deriv phi x = (Real.exp x - 1) / x - (Real.exp x - (1 + x)) / x ^ 2 := by
      rw [(hasDerivAt_phi hx).deriv]
      field_simp [hx]
      ring
    rw [hvalue]
    refine (h₁.sub h₂).congr_fun fun j => ?_
    change phiSeriesTerm x 1 j = x ^ j / ((j + 1).factorial : ℝ) -
      x ^ j / (((j + 1) + 1).factorial : ℝ)
    rw [cast_factorial_succ (j + 1), cast_factorial_succ j]
    simp only [phiSeriesTerm, Nat.cast_add, Nat.cast_one]
    field_simp (disch := positivity)
    ring
  · have hvalue : deriv (deriv phi) x = (Real.exp x - 1) / x -
        2 * ((Real.exp x - (1 + x)) / x ^ 2) +
        2 * ((Real.exp x - (1 + x + x ^ 2 / 2)) / x ^ 3) := by
      rw [(hasDerivAt_deriv_phi hx).deriv]
      field_simp [hx]
      ring
    rw [hvalue]
    refine ((h₁.sub (h₂.mul_left 2)).add (h₃.mul_left 2)).congr_fun fun j => ?_
    change phiSeriesTerm x 2 j = x ^ j / ((j + 1).factorial : ℝ) -
      2 * (x ^ j / (((j + 1) + 1).factorial : ℝ)) +
      2 * (x ^ j / (((j + 2) + 1).factorial : ℝ))
    rw [cast_factorial_succ (j + 2), cast_factorial_succ (j + 1), cast_factorial_succ j]
    simp only [phiSeriesTerm, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp (disch := positivity)
    ring

private theorem phiSeriesTerm_succ_le {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (k j : ℕ) : phiSeriesTerm x k (j + 1) ≤ phiSeriesTerm x k j * (1 / 2) := by
  simp only [phiSeriesTerm, pow_succ, cast_factorial_succ, Nat.cast_add, Nat.cast_one]
  have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hf : (j.factorial : ℝ) ≤ ((j : ℝ) + 1) * (j.factorial : ℝ) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hj (show 0 ≤ (j.factorial : ℝ) by positivity)
  calc
    _ ≤ (x ^ j * x) / ((j.factorial : ℝ) * ((j : ℝ) + (k : ℝ) + 1)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul hf (by linarith) (by positivity) (by positivity)
    _ = (x ^ j / ((j.factorial : ℝ) * ((j : ℝ) + (k : ℝ) + 1))) * x :=
      mul_div_right_comm _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hxhalf (by positivity)

private theorem phiSeries_partial_bounds {x y : ℝ} {k : ℕ} (hx : 0 ≤ x) (hxmax : x ≤ 9 / 32)
    (hs : HasSum (phiSeriesTerm x k) y) :
    phiSeriesPartial x k ≤ y ∧ y ≤ phiSeriesPartial x k + 1 / (2 : ℝ) ^ 128 := by
  have hxhalf : x ≤ 1 / 2 := hxmax.trans (by norm_num)
  have hcomparison (n : ℕ) : phiSeriesTerm x k (n + 32) ≤
      phiSeriesTerm x k 32 * (1 / 2 : ℝ) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.succ_add, pow_succ]
        calc
          _ ≤ phiSeriesTerm x k (n + 32) * (1 / 2 : ℝ) := phiSeriesTerm_succ_le hx hxhalf k _
          _ ≤ _ := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right ih (by norm_num)
  have htail : HasSum (fun j : ℕ => phiSeriesTerm x k (j + 32)) (y - phiSeriesPartial x k) :=
    (hasSum_nat_add_iff' 32 (f := phiSeriesTerm x k) (g := y)).2 hs
  have htail_le :=
    hasSum_le hcomparison htail (hasSum_geometric_two.mul_left (phiSeriesTerm x k 32))
  have hfirst : phiSeriesTerm x k 32 ≤ (9 / 32 : ℝ) ^ 32 / (Nat.factorial 32 : ℝ) := by
    unfold phiSeriesTerm
    calc
      _ ≤ x ^ 32 / (Nat.factorial 32 : ℝ) := by
        apply div_le_div_of_nonneg_left (pow_nonneg hx _) (by positivity)
        have hden : (1 : ℝ) ≤ (32 : ℝ) + (k : ℝ) + 1 := by
          linarith [Nat.cast_nonneg (α := ℝ) k]
        simpa only [Nat.cast_ofNat, mul_one] using
          mul_le_mul_of_nonneg_left hden (show 0 ≤ (Nat.factorial 32 : ℝ) by positivity)
      _ ≤ _ := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxmax 32) (by positivity)
  have hsmall : (9 / 32 : ℝ) ^ 32 / (Nat.factorial 32 : ℝ) * 2 ≤ 1 / 2 ^ 128 := by
    norm_num
  refine ⟨?_, ?_⟩
  · rw [← hs.tsum_eq]
    exact hs.summable.sum_le_tsum (Finset.range 32) fun j _ => by
      unfold phiSeriesTerm
      positivity
  · have htwice := mul_le_mul_of_nonneg_right hfirst (by norm_num : (0 : ℝ) ≤ 2)
    have herror := htail_le.trans (htwice.trans hsmall)
    simpa only [add_comm] using sub_le_iff_le_add.mp herror

/-- Two-sided enclosures for the three actual values used by the near-zero cover. -/
theorem phiSeries_bounds {x : ℝ} (hx : 0 < x) (hxmax : x ≤ 9 / 32) :
    (phiSeriesPartial x 0 ≤ phi x ∧ phi x ≤ phiSeriesPartial x 0 + 1 / (2 : ℝ) ^ 128) ∧
    (phiSeriesPartial x 1 ≤ deriv phi x ∧ deriv phi x ≤ phiSeriesPartial x 1 + 1 / (2 : ℝ) ^ 128) ∧
    (phiSeriesPartial x 2 ≤ deriv (deriv phi) x ∧
      deriv (deriv phi) x ≤ phiSeriesPartial x 2 + 1 / (2 : ℝ) ^ 128) := by
  obtain ⟨h₀, h₁, h₂⟩ := hasSum_phiSeries hx.ne'
  exact ⟨phiSeries_partial_bounds hx.le hxmax h₀, phiSeries_partial_bounds hx.le hxmax h₁,
    phiSeries_partial_bounds hx.le hxmax h₂⟩

end RefinedBMV.FourSpectrumLift

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-! Omega original.

The magnetic proper-time coefficient and estimates for the electric exponential series. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace Omega.EulerHeisenbergProperTime

theorem properTimeMoment (m : ℝ) (hm : 0 < m) :
    (∫ s in Ioi (0 : ℝ), s * Real.exp (-(m ^ 2) * s)) = 1 / m ^ 4 := by
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := m ^ 2)
    (by norm_num) (sq_pos_of_pos hm)
  have hGamma : Real.Gamma 2 = 1 := by simp
  rw [show (2 : ℝ) - 1 = 1 by norm_num, hGamma, mul_one] at hg
  simpa only [Real.rpow_one, Real.rpow_two, neg_mul, div_pow, one_pow, ← pow_mul] using hg

theorem magneticQuarticCoefficient (e m B : ℝ) (hm : 0 < m) :
    ((e * B) ^ 4 / (360 * Real.pi ^ 2)) *
        (∫ s in Ioi (0 : ℝ), s * Real.exp (-(m ^ 2) * s)) =
      (2 * (e ^ 2 / (4 * Real.pi)) ^ 2 / (45 * m ^ 4)) * B ^ 4 := by
  rw [properTimeMoment m hm]
  field_simp [ne_of_gt hm, Real.pi_ne_zero]
  ring

theorem sinhTaylor5 :
    Tendsto (fun x : ℝ => (Real.sinh x - (x + x ^ 3 / 6 + x ^ 5 / 120)) / x ^ 5)
      (𝓝 0) (𝓝 0) := by
  have h := (taylor_isLittleO_univ (x₀ := 0) (n := 5)
    Real.contDiff_sinh).tendsto_div_nhds_zero
  refine h.congr fun x => ?_
  norm_num [taylor_within_apply, Finset.sum_range_succ, iteratedDerivWithin_univ,
    Real.iteratedDeriv_add_one_sinh, Real.iteratedDeriv_add_one_cosh,
    iteratedDeriv_zero, Nat.factorial_succ, smul_eq_mul]
  ring

theorem coshTaylor4 :
    Tendsto (fun x : ℝ => (Real.cosh x - (1 + x ^ 2 / 2 + x ^ 4 / 24)) / x ^ 4)
      (𝓝 0) (𝓝 0) := by
  have h := (taylor_isLittleO_univ (x₀ := 0) (n := 4)
    Real.contDiff_cosh).tendsto_div_nhds_zero
  refine h.congr fun x => ?_
  norm_num [taylor_within_apply, Finset.sum_range_succ, iteratedDerivWithin_univ,
    Real.iteratedDeriv_add_one_sinh, Real.iteratedDeriv_add_one_cosh,
    iteratedDeriv_zero, Nat.factorial_succ, smul_eq_mul]
  ring

theorem sinhDiv :
    Tendsto (fun x : ℝ => Real.sinh x / x) (𝓝[≠] 0) (𝓝 1) := by
  have h := (Real.isEquivalent_sinh.isLittleO.tendsto_div_nhds_zero).mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  have h' := h.add_const 1
  simp only [zero_add] at h'
  refine h'.congr' ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := {0}ᶜ)] with x hx
  change x ≠ 0 at hx
  change (Real.sinh x - x) / x + 1 = Real.sinh x / x
  field_simp
  ring

def electricTerm (t : ℝ) (n : ℕ) : ℝ :=
  (1 / ((n : ℝ) + 1) ^ 2) * Real.exp (-(((n : ℝ) + 1) * t))

def electricSeries (t : ℝ) : ℝ := ∑' n : ℕ, electricTerm t n

private theorem zetaTail :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2)
    (g := Real.pi ^ 2 / 6) 1).mpr (by simpa using hasSum_zeta_two)
  simpa [Finset.sum_range_one, Nat.cast_add] using h

private theorem electricTerm_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    electricTerm t n ≤ (1 / ((n : ℝ) + 1) ^ 2) * Real.exp (-t) := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) ht]

theorem electricTermSummable (t : ℝ) (ht : 0 ≤ t) : Summable (electricTerm t) :=
  Summable.of_nonneg_of_le (fun _ => by unfold electricTerm; positivity)
    (electricTerm_le t ht) (zetaTail.summable.mul_right _)

theorem electricSeries_bounds (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ electricSeries t ∧
      electricSeries t ≤ (Real.pi ^ 2 / 6) * Real.exp (-t) := by
  have hsum := electricTermSummable t ht
  constructor
  · have h := hsum.le_tsum 0 (fun n _ => by unfold electricTerm; positivity)
    simpa [electricSeries, electricTerm] using h
  · exact (hsum.tsum_le_tsum (electricTerm_le t ht) (zetaTail.summable.mul_right _)).trans_eq
      (zetaTail.mul_right (Real.exp (-t))).tsum_eq

theorem exponentialFlat (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Tendsto (fun x : ℝ => Real.exp (-(a / x)) / x ^ k) (𝓝[>] 0) (𝓝 0) := by
  have hx : Tendsto (fun x : ℝ => a / x) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop ha
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hx).div_const (a ^ k)
  simp only [zero_div] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with x hx
  have hx' : x ≠ 0 := ne_of_gt hx
  change (a / x) ^ k * Real.exp (-(a / x)) / a ^ k = _
  rw [div_pow]
  field_simp [pow_ne_zero k (ne_of_gt ha), pow_ne_zero k hx']

end Omega.EulerHeisenbergProperTime

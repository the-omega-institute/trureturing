/- GID: D5/S3/Analysis/ThermalIntegrals
   generality: G
   mirror-B: none(waiver:covered-by-hawking-unruh-thermal-radiation4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The cubic Bose integral is a sum of positive exponential moments. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Omega original.

The cubic Bose integral is a sum of positive exponential moments. Subtracting a
rescaled Bose integrand gives the cubic Fermi integral on the same half-line.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace Omega

private def cubicExpMoment (n : ℕ) (x : ℝ) : ℝ :=
  x ^ 3 * Real.exp (-((↑(n + 1) : ℝ) * x))

private theorem cubicExpMoment_integral (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), cubicExpMoment n x) = 6 / (↑(n + 1) : ℝ) ^ 4 := by
  have hgamma : Real.Gamma 4 = 6 := by
    have harg : (↑(3 : ℕ) : ℝ) + 1 = 4 := by norm_num
    have hfac : (↑(Nat.factorial 3) : ℝ) = 6 := by norm_num [Nat.factorial]
    simpa only [harg, hfac] using Real.Gamma_nat_eq_factorial 3
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 4) (r := ↑(n + 1))
    (by norm_num) (by positivity)
  rw [hgamma, show (4 : ℝ) - 1 = (↑(3 : ℕ) : ℝ) by norm_num,
    show (4 : ℝ) = (↑(4 : ℕ) : ℝ) by norm_num] at h
  simp only [Real.rpow_natCast, div_pow, one_pow] at h
  exact h.trans (by rw [mul_comm, mul_one_div])

private theorem cubicExpMoment_sum {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ cubicExpMoment n x) (x ^ 3 / (Real.exp x - 1)) := by
  have hq : Real.exp (-x) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_neg_of_pos hx)
  have hsum := (hasSum_geometric_of_lt_one (Real.exp_nonneg (-x)) hq).mul_left
    (x ^ 3 * Real.exp (-x))
  have hden : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)
  convert hsum using 1
  · ext n
    rw [cubicExpMoment, ← mul_neg, Real.exp_nat_mul, pow_succ]
    ring
  · rw [Real.exp_neg]
    field_simp [(Real.exp_pos x).ne', hden.ne']

/-- The cubic Bose integral on the positive half-line is six times the fourth zeta value. -/
theorem bose_einstein_cubic_integral :
    (∫ x in Ioi (0 : ℝ), x ^ 3 / (Real.exp x - 1)) = Real.pi ^ 4 / 15 := by
  have hterm (n : ℕ) : IntegrableOn (cubicExpMoment n) (Ioi (0 : ℝ)) :=
    .of_integral_ne_zero (by rw [cubicExpMoment_integral]; positivity)
  have hnorm (n : ℕ) :
      (∫ x in Ioi (0 : ℝ), ‖cubicExpMoment n x‖) = 6 / (↑(n + 1) : ℝ) ^ 4 := by
    rw [← cubicExpMoment_integral n]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx' : 0 < x := mem_Ioi.mp hx
    exact Real.norm_of_nonneg (by unfold cubicExpMoment; positivity)
  have hz : HasSum (fun n : ℕ ↦ 6 / (↑(n + 1) : ℝ) ^ 4) (Real.pi ^ 4 / 15) := by
    have h := (hasSum_nat_add_iff' 1).2 (hasSum_zeta_four.mul_left 6)
    have hlim : (6 : ℝ) * (Real.pi ^ 4 / 90) = Real.pi ^ 4 / 15 := by ring
    rw [hlim] at h
    simpa [Finset.sum_range_one, div_eq_mul_inv] using h
  have hns : Summable (fun n ↦ ∫ x in Ioi (0 : ℝ), ‖cubicExpMoment n x‖) := by
    simpa only [hnorm] using hz.summable
  have h := hasSum_integral_of_summable_integral_norm hterm hns
  have heq := (show HasSum (fun n ↦ ∫ x in Ioi (0 : ℝ), cubicExpMoment n x)
      (Real.pi ^ 4 / 15) by simpa only [cubicExpMoment_integral] using hz).unique h
  rw [heq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact (cubicExpMoment_sum (mem_Ioi.mp hx)).tsum_eq.symm

/-- Substitution by twice the integration variable yields the factor `7 / 8`. -/
theorem fermi_dirac_cubic_integral :
    (∫ x in Ioi (0 : ℝ), x ^ 3 / (Real.exp x + 1)) = (7 / 8) * (Real.pi ^ 4 / 15) := by
  let bose := fun x : ℝ ↦ x ^ 3 / (Real.exp x - 1)
  let scaled := fun x : ℝ ↦ x ^ 3 / (Real.exp (2 * x) - 1)
  have hbose : IntegrableOn bose (Ioi (0 : ℝ)) :=
    .of_integral_ne_zero (by dsimp [bose]; rw [bose_einstein_cubic_integral]; positivity)
  have hscaledBose : IntegrableOn (fun x ↦ bose (2 * x)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff bose 0 zero_lt_two).mpr
    simpa only [mul_zero] using hbose
  have hscaled_eq : scaled = fun x ↦ (1 / 8) * bose (2 * x) := by
    ext x
    dsimp [scaled, bose]
    ring
  have hscaled : IntegrableOn scaled (Ioi (0 : ℝ)) := by
    rw [hscaled_eq]
    exact hscaledBose.const_mul _
  have hscaled_integral : (∫ x in Ioi (0 : ℝ), scaled x) =
      (1 / 16) * ∫ x in Ioi (0 : ℝ), bose x := by
    rw [hscaled_eq, integral_const_mul, integral_comp_mul_left_Ioi bose 0 zero_lt_two]
    simp only [mul_zero, smul_eq_mul]
    ring
  calc
    _ = ∫ x in Ioi (0 : ℝ), bose x - 2 * scaled x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx' : 0 < x := mem_Ioi.mp hx
      have hm : Real.exp x - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx')).ne'
      have hp : Real.exp x + 1 ≠ 0 := by positivity
      have hfactor : Real.exp (2 * x) - 1 = (Real.exp x - 1) * (Real.exp x + 1) := by
        rw [two_mul x, Real.exp_add]
        ring
      dsimp [bose, scaled]
      rw [hfactor]
      field_simp [hm, hp]
      ring
    _ = (∫ x in Ioi (0 : ℝ), bose x) - 2 * (∫ x in Ioi (0 : ℝ), scaled x) := by
      rw [integral_sub hbose (hscaled.const_mul _), integral_const_mul]
    _ = (7 / 8) * (Real.pi ^ 4 / 15) := by
      rw [hscaled_integral]
      simp only [bose, bose_einstein_cubic_integral]
      ring

end Omega

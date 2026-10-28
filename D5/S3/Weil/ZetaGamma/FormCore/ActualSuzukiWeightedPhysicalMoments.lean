/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiWeightedPhysicalMoments
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/FormCore/ActualSuzukiWeightedPhysicalMoments
   mirror-E: none(waiver:analytic-physical-moment-estimates)
   anchors: []
   utility: none
   digest: Original H6 physical product domains and weighted trace and logarithmic moment bounds. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Weil.ZetaGamma.FormCore.SourceOriginalMeanZeroGamma

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open scoped ENNReal Topology

private abbrev dualTime : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

private def dualDensity00 (s : ℝ) : ℝ :=
  (s ^ (5 / 4 : ℝ) - 1) ^ 2 / (s ^ 6 - 1)

private def dualDensity11 (s : ℝ) : ℝ :=
  Real.log s ^ 2 / (s ^ 6 - 1)

private def dualTimeDensity00 (t : ℝ) : ℝ :=
  (Real.exp ((5 / 4 : ℝ) * t) - 1) ^ 2 * Real.exp t /
    (Real.exp (6 * t) - 1)

private def dualTimeDensity11 (t : ℝ) : ℝ :=
  t ^ 2 * Real.exp t / (Real.exp (6 * t) - 1)

private def dualRate (n : ℕ) : ℝ := 6 * ((n : ℝ) + 1) - 1

private def dualLayer00 (n : ℕ) (t : ℝ) : ℝ :=
  (Real.exp ((5 / 4 : ℝ) * t) - 1) ^ 2 * Real.exp (-(dualRate n) * t)

private def dualLayer11 (n : ℕ) (t : ℝ) : ℝ :=
  t ^ 2 * Real.exp (-(dualRate n) * t)

private def dualCoefficient00 (n : ℕ) : ℝ :=
  1 / (dualRate n - 5 / 2) - 2 / (dualRate n - 5 / 4) + 1 / dualRate n

private def dualCoefficient11 (n : ℕ) : ℝ := 2 / dualRate n ^ 3

private def dualMajorant00 (x : ℝ) : ℝ := (25 / 8 : ℝ) / (6 * x - 7 / 2) ^ 3
private def dualMajorant11 (x : ℝ) : ℝ := 2 / (6 * x - 1) ^ 3

private theorem dual_rate_ge_five (n : ℕ) : 5 ≤ dualRate n := by
  unfold dualRate
  linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem dual_rpow_neg_three (x : ℝ) :
    x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
  norm_num [Real.rpow_neg_ofNat]

/- A real change of variables pays the actual affine-cube domain and
integral before the integral test uses it. -/
private theorem dual_affine_cube_domain_integral (N d K : ℝ)
    (hB : 0 < 6 * N - d) :
    IntegrableOn (fun x : ℝ => K / (6 * x - d) ^ 3) (Ioi N) ∧
      (∫ x : ℝ in Ioi N, K / (6 * x - d) ^ 3) =
        K / (12 * (6 * N - d) ^ 2) := by
  let φ : ℝ → ℝ := fun x => 6 * x - d
  have hφ : ∀ x ∈ Ioi N, HasDerivWithinAt φ 6 (Ioi N) x := by
    intro x hx
    simpa only [φ, mul_one, id_eq] using
      (((hasDerivAt_id x).const_mul 6).sub_const d).hasDerivWithinAt
  have hInj : InjOn φ (Ioi N) := by
    intro x hx y hy hxy
    dsimp only [φ] at hxy
    linarith
  have hImage : φ '' Ioi N = Ioi (6 * N - d) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change 6 * N - d < 6 * x - d
      linarith [show N < x from hx]
    · intro hy
      refine ⟨(y + d) / 6, ?_, ?_⟩
      · change N < (y + d) / 6
        linarith [show 6 * N - d < y from hy]
      · dsimp only [φ]
        ring
  have hgi : IntegrableOn (fun y : ℝ => y ^ (-3 : ℝ))
      (Ioi (6 * N - d)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hB
  have hScaled : IntegrableOn (fun x : ℝ => 6 * (6 * x - d) ^ (-3 : ℝ))
      (Ioi N) := by
    have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hφ hInj (fun y : ℝ => y ^ (-3 : ℝ))).1
      (by simpa only [hImage] using hgi)
    simpa only [φ, abs_of_pos (by norm_num : (0 : ℝ) < 6), smul_eq_mul] using h
  have hi : IntegrableOn (fun x : ℝ => K / (6 * x - d) ^ 3) (Ioi N) := by
    apply (hScaled.const_mul (K / 6)).congr
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [dual_rpow_neg_three]
      ring
  have hChange : (∫ y : ℝ in Ioi (6 * N - d), y ^ (-3 : ℝ)) =
      ∫ x : ℝ in Ioi N, 6 * (6 * x - d) ^ (-3 : ℝ) := by
    simpa only [hImage, φ, abs_of_pos (by norm_num : (0 : ℝ) < 6), smul_eq_mul] using
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hφ hInj
        (fun y : ℝ => y ^ (-3 : ℝ))
  refine ⟨hi, ?_⟩
  calc
    _ = (K / 6) * ∫ x : ℝ in Ioi N, 6 * (6 * x - d) ^ (-3 : ℝ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [dual_rpow_neg_three]
        ring
    _ = (K / 6) * ∫ y : ℝ in Ioi (6 * N - d), y ^ (-3 : ℝ) := by rw [hChange]
    _ = (K / 6) * (-(6 * N - d) ^ (-2 : ℝ) / (-2 : ℝ)) := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hB]
      norm_num
    _ = _ := by
      norm_num [Real.rpow_neg_ofNat]
      field_simp [hB.ne']
      <;> ring

private theorem dual_affine_cube_antitone (N d K : ℝ)
    (hB : 0 < 6 * N - d) (hK : 0 ≤ K) :
    AntitoneOn (fun x : ℝ => K / (6 * x - d) ^ 3) (Ici N) := by
  intro x hx y hy hxy
  have hx0 : 0 < 6 * x - d := by linarith [show N ≤ x from hx]
  have hy0 : 0 < 6 * y - d := by linarith [show N ≤ y from hy]
  exact div_le_div_of_nonneg_left hK (pow_pos hx0 3)
    (by gcongr)

private theorem dual_majorant00_domain_integral :
    IntegrableOn dualMajorant00 (Ioi 2) ∧
      (∫ x : ℝ in Ioi 2, dualMajorant00 x) = 25 / 6936 := by
  have h := dual_affine_cube_domain_integral 2 (7 / 2) (25 / 8) (by norm_num)
  norm_num [dualMajorant00] at h ⊢
  exact h

private theorem dual_majorant11_domain_integral :
    IntegrableOn dualMajorant11 (Ioi 3) ∧
      (∫ x : ℝ in Ioi 3, dualMajorant11 x) = 1 / 1734 := by
  have h := dual_affine_cube_domain_integral 3 1 2 (by norm_num)
  norm_num [dualMajorant11] at h ⊢
  exact h

private theorem dual_coefficient00_positive_formula (n : ℕ) :
    dualCoefficient00 n = (25 / 8 : ℝ) /
      (dualRate n * (dualRate n - 5 / 4) * (dualRate n - 5 / 2)) := by
  have hb := dual_rate_ge_five n
  unfold dualCoefficient00
  have h2 : dualRate n * 2 - 5 ≠ 0 := by linarith
  have h4 : dualRate n * 4 - 5 ≠ 0 := by linarith
  have hp : 25 - dualRate n * 30 + dualRate n ^ 2 * 8 ≠ 0 := by
    have : 0 < 25 - dualRate n * 30 + dualRate n ^ 2 * 8 := by
      nlinarith [sq_nonneg (dualRate n - 5)]
    exact this.ne'
  field_simp [show dualRate n ≠ 0 by linarith,
    show dualRate n - 5 / 4 ≠ 0 by linarith,
    show dualRate n - 5 / 2 ≠ 0 by linarith, h2, h4, hp]
  <;> ring

private theorem dual_coefficient00_nonneg (n : ℕ) : 0 ≤ dualCoefficient00 n := by
  rw [dual_coefficient00_positive_formula]
  have hb := dual_rate_ge_five n
  have hb0 : 0 < dualRate n := by linarith
  have hb1 : 0 < dualRate n - 5 / 4 := by linarith
  have hb2 : 0 < dualRate n - 5 / 2 := by linarith
  positivity

private theorem dual_coefficient00_majorant (n : ℕ) :
    dualCoefficient00 n ≤ dualMajorant00 ((n : ℝ) + 1) := by
  have hb := dual_rate_ge_five n
  have h0 : 0 < dualRate n - 5 / 2 := by linarith
  rw [dual_coefficient00_positive_formula]
  unfold dualMajorant00
  rw [show 6 * ((n : ℝ) + 1) - 7 / 2 = dualRate n - 5 / 2 by
    unfold dualRate; ring]
  apply div_le_div_of_nonneg_left (by norm_num) (pow_pos h0 3)
  calc
    _ = (dualRate n - 5 / 2) * (dualRate n - 5 / 2) *
        (dualRate n - 5 / 2) := by ring
    _ ≤ _ := by gcongr <;> linarith

private theorem dual_majorant00_nat_summable :
    Summable (fun n : ℕ => dualMajorant00 n) := by
  apply AntitoneOn.summable_of_integrableOn_Ioi (N := 2)
    (dual_affine_cube_antitone 2 (7 / 2) (25 / 8) (by norm_num) (by norm_num))
    dual_majorant00_domain_integral.1
  intro x hx
  change 0 ≤ (25 / 8 : ℝ) / (6 * x - 7 / 2) ^ 3
  have : 0 < 6 * x - 7 / 2 := by linarith [show (2 : ℝ) < x from hx]
  positivity

private theorem dual_majorant11_nat_summable :
    Summable (fun n : ℕ => dualMajorant11 n) := by
  apply AntitoneOn.summable_of_integrableOn_Ioi (N := 3)
    (dual_affine_cube_antitone 3 1 2 (by norm_num) (by norm_num))
    dual_majorant11_domain_integral.1
  intro x hx
  change 0 ≤ (2 : ℝ) / (6 * x - 1) ^ 3
  have : 0 < 6 * x - 1 := by linarith [show (3 : ℝ) < x from hx]
  positivity

private theorem dual_coefficient00_summable : Summable dualCoefficient00 := by
  apply Summable.of_nonneg_of_le dual_coefficient00_nonneg
    dual_coefficient00_majorant
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 dual_majorant00_nat_summable

private theorem dual_coefficient11_summable : Summable dualCoefficient11 := by
  apply ((summable_nat_add_iff 1).2 dual_majorant11_nat_summable).congr
  intro n
  simp only [dualCoefficient11, dualMajorant11, dualRate, Nat.cast_add, Nat.cast_one]

private theorem dual_coefficient00_series_bound :
    (∑' n : ℕ, dualCoefficient00 n) ≤ 3 / 40 := by
  have htail : (∑' n : ℕ, dualCoefficient00 (n + 2)) ≤ 25 / 6936 := by
    calc
      _ ≤ ∑' n : ℕ, dualMajorant00 ((n + 2 + 1 : ℕ) : ℝ) := by
        apply ((summable_nat_add_iff 2).2 dual_coefficient00_summable).tsum_le_tsum
          (fun n => by simpa only [Nat.cast_add, Nat.cast_one] using
            dual_coefficient00_majorant (n + 2))
        simpa only [Nat.add_assoc] using
          (summable_nat_add_iff 3).2 dual_majorant00_nat_summable
      _ ≤ ∫ x : ℝ in Ioi 2, dualMajorant00 x := by
        apply AntitoneOn.tsum_comp_add_le_integral 2
          (dual_affine_cube_antitone 2 (7 / 2) (25 / 8) (by norm_num) (by norm_num))
          dual_majorant00_domain_integral.1
        intro x hx
        change 0 ≤ (25 / 8 : ℝ) / (6 * x - 7 / 2) ^ 3
        have : 0 < 6 * x - 7 / 2 := by linarith [show (2 : ℝ) < x from hx]
        positivity
      _ = _ := dual_majorant00_domain_integral.2
  rw [← dual_coefficient00_summable.sum_add_tsum_nat_add 2]
  have hprefix : (∑ n ∈ Finset.range 2, dualCoefficient00 n) =
      (1 / 15 : ℝ) + (2 / 17 - 8 / 39 + 1 / 11) := by
    norm_num [Finset.sum_range_succ, dualCoefficient00, dualRate]
  rw [hprefix]
  linarith

private theorem dual_coefficient11_series_bound :
    (∑' n : ℕ, dualCoefficient11 n) ≤ 3 / 160 := by
  have htail : (∑' n : ℕ, dualCoefficient11 (n + 3)) ≤ 1 / 1734 := by
    have h := AntitoneOn.tsum_comp_add_le_integral 3
      (dual_affine_cube_antitone 3 1 2 (by norm_num) (by norm_num))
      dual_majorant11_domain_integral.1 (fun x hx => by
        change 0 ≤ (2 : ℝ) / (6 * x - 1) ^ 3
        have : 0 < 6 * x - 1 := by linarith [show (3 : ℝ) < x from hx]
        positivity)
    change (∑' n : ℕ, dualMajorant11 ((n + 3 + 1 : ℕ) : ℝ)) ≤
      ∫ x : ℝ in Ioi 3, dualMajorant11 x at h
    rw [dual_majorant11_domain_integral.2] at h
    have hsum : (∑' n : ℕ, dualCoefficient11 (n + 3)) =
        ∑' n : ℕ, dualMajorant11 ((n + 3 + 1 : ℕ) : ℝ) := by
      apply tsum_congr
      intro n
      unfold dualCoefficient11 dualMajorant11 dualRate
      have heq : 6 * (((n + 3 : ℕ) : ℝ) + 1) - 1 =
          6 * ((n + 3 + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
      exact congrArg (fun z : ℝ => 2 / z ^ 3) heq
    rw [hsum]
    exact h
  rw [← dual_coefficient11_summable.sum_add_tsum_nat_add 3]
  have hprefix : (∑ n ∈ Finset.range 3, dualCoefficient11 n) =
      (2 / 125 : ℝ) + 2 / 1331 + 2 / 4913 := by
    norm_num [Finset.sum_range_succ, dualCoefficient11, dualRate]
  rw [hprefix]
  linarith

private theorem dual_layer00_expansion (n : ℕ) (t : ℝ) :
    dualLayer00 n t = Real.exp (-(dualRate n - 5 / 2) * t) -
      2 * Real.exp (-(dualRate n - 5 / 4) * t) + Real.exp (-(dualRate n) * t) := by
  have hq : Real.exp ((5 / 4 : ℝ) * t) ^ 2 * Real.exp (-(dualRate n) * t) =
      Real.exp (-(dualRate n - 5 / 2) * t) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hl : Real.exp ((5 / 4 : ℝ) * t) * Real.exp (-(dualRate n) * t) =
      Real.exp (-(dualRate n - 5 / 4) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp ((5 / 4 : ℝ) * t) ^ 2 * Real.exp (-(dualRate n) * t) -
        2 * (Real.exp ((5 / 4 : ℝ) * t) * Real.exp (-(dualRate n) * t)) +
          Real.exp (-(dualRate n) * t) := by unfold dualLayer00; ring
    _ = _ := by rw [hq, hl]

private theorem dual_laplace_domain_integral {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ => Real.exp (-b * t)) dualTime ∧
      (∫ t : ℝ, Real.exp (-b * t) ∂dualTime) = 1 / b := by
  refine ⟨integrableOn_exp_mul_Ioi (by linarith : -b < 0) 0, ?_⟩
  simpa only [mul_zero, Real.exp_zero, neg_div_neg_eq] using
    integral_exp_mul_Ioi (by linarith : -b < 0) 0

private theorem dual_layer00_domain_integral (n : ℕ) :
    Integrable (dualLayer00 n) dualTime ∧
      (∫ t : ℝ, dualLayer00 n t ∂dualTime) = dualCoefficient00 n := by
  have hb := dual_rate_ge_five n
  have hA := dual_laplace_domain_integral (by linarith : 0 < dualRate n - 5 / 2)
  have hB := dual_laplace_domain_integral (by linarith : 0 < dualRate n - 5 / 4)
  have hC := dual_laplace_domain_integral (by linarith : 0 < dualRate n)
  have hfun : dualLayer00 n = fun t : ℝ =>
      Real.exp (-(dualRate n - 5 / 2) * t) -
        2 * Real.exp (-(dualRate n - 5 / 4) * t) + Real.exp (-(dualRate n) * t) :=
    funext (dual_layer00_expansion n)
  rw [hfun]
  refine ⟨(hA.1.sub (hB.1.const_mul 2)).add hC.1, ?_⟩
  have hAdd := integral_add (hA.1.sub (hB.1.const_mul 2)) hC.1
  have hSub := integral_sub hA.1 (hB.1.const_mul 2)
  dsimp only [Pi.sub_apply, Pi.add_apply] at hAdd hSub
  dsimp only
  rw [hAdd, hSub, integral_const_mul, hA.2, hB.2, hC.2]
  unfold dualCoefficient00
  ring

private theorem dual_layer11_domain_integral (n : ℕ) :
    Integrable (dualLayer11 n) dualTime ∧
      (∫ t : ℝ, dualLayer11 n t ∂dualTime) = dualCoefficient11 n := by
  have hb : 0 < dualRate n := lt_of_lt_of_le (by norm_num) (dual_rate_ge_five n)
  have hi : Integrable (dualLayer11 n) dualTime := by
    have hbase : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ 2) (Ioi 0) := by
      simpa only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_ofNat] using
        Real.GammaIntegral_convergent (s := (3 : ℝ)) (by norm_num)
    have hscaled : IntegrableOn
        (fun t : ℝ => Real.exp (-(dualRate n * t)) * (dualRate n * t) ^ 2)
        (Ioi 0) := by
      apply (integrableOn_Ioi_comp_mul_left_iff
        (fun y : ℝ => Real.exp (-y) * y ^ 2) 0 hb).2
      simpa only [mul_zero] using hbase
    apply (hscaled.const_mul ((dualRate n)⁻¹ ^ 2)).congr
    exact Eventually.of_forall fun t => by
      unfold dualLayer11
      simp only [neg_mul]
      field_simp [hb.ne']
      <;> ring
  refine ⟨hi, ?_⟩
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 : ℝ)) (r := dualRate n) (by norm_num) hb
  have hg : Real.Gamma (3 : ℝ) = 2 := by norm_num
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_ofNat, hg] at h
  change (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-(dualRate n) * t)) = _
  simp_rw [neg_mul] at h ⊢
  rw [h]
  unfold dualCoefficient11
  field_simp [hb.ne']
  <;> ring

/- Positive geometric series for the genuine logarithmic-coordinate
density. The lower endpoint t=0 is excluded by the actual Ioi domain. -/
private theorem dual_exponential_positive_series {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-(dualRate n) * t))
      (Real.exp t / (Real.exp (6 * t) - 1)) := by
  have hr0 : 0 ≤ Real.exp (-6 * t) := (Real.exp_pos _).le
  have hr1 : Real.exp (-6 * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hden : Real.exp (6 * t) - 1 ≠ 0 := by
    have : 1 < Real.exp (6 * t) := by rw [Real.one_lt_exp_iff]; positivity
    linarith
  have hneg : -6 * t = -(6 * t) := by ring
  have hi : 1 - (Real.exp (6 * t))⁻¹ ≠ 0 := by
    rw [← Real.exp_neg, ← hneg]
    linarith
  have hValue : Real.exp (-5 * t) * (1 - Real.exp (-6 * t))⁻¹ =
      Real.exp t / (Real.exp (6 * t) - 1) := by
    rw [hneg, Real.exp_neg]
    calc
      _ = (Real.exp (-5 * t) * Real.exp (6 * t)) /
          (Real.exp (6 * t) - 1) := by
        field_simp [Real.exp_ne_zero, hden, hi]
        <;> ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hrow (n : ℕ) : Real.exp (-(dualRate n) * t) =
      Real.exp (-5 * t) * Real.exp (-6 * t) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    unfold dualRate
    congr 1
    ring
  have hfun : (fun n : ℕ => Real.exp (-(dualRate n) * t)) =
      fun n : ℕ => Real.exp (-5 * t) * Real.exp (-6 * t) ^ n := funext hrow
  rw [hfun]
  simpa only [hValue] using
    (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-5 * t))

private theorem dual_layer00_positive_series {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => dualLayer00 n t) (dualTimeDensity00 t) := by
  simpa only [dualLayer00, dualTimeDensity00, div_eq_mul_inv, mul_assoc] using
    (dual_exponential_positive_series ht).mul_left
      ((Real.exp ((5 / 4 : ℝ) * t) - 1) ^ 2)

private theorem dual_layer11_positive_series {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => dualLayer11 n t) (dualTimeDensity11 t) := by
  simpa only [dualLayer11, dualTimeDensity11, div_eq_mul_inv, mul_assoc] using
    (dual_exponential_positive_series ht).mul_left (t ^ 2)

/- Nonnegative Tonelli pays both the domain and the actual integral.
All summability hypotheses below are proved by the concrete integral test
above before this helper is consumed. -/
private theorem dual_positive_series_domain_integral
    (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (q : ℕ → ℝ)
    (hFm : ∀ n : ℕ, Measurable (F n))
    (hFp : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ F n t)
    (hFi : ∀ n : ℕ, Integrable (F n) dualTime)
    (hFq : ∀ n : ℕ, (∫ t : ℝ, F n t ∂dualTime) = q n)
    (hqs : Summable q) (hfm : AEStronglyMeasurable f dualTime)
    (hfp : 0 ≤ᵐ[dualTime] f)
    (hpoint : ∀ᵐ t : ℝ ∂dualTime, HasSum (fun n : ℕ => F n t) (f t)) :
    Integrable f dualTime ∧ (∫ t : ℝ, f t ∂dualTime) = ∑' n : ℕ, q n := by
  have hqp (n : ℕ) : 0 ≤ q n := by
    rw [← hFq n]
    exact integral_nonneg (hFp n)
  have hLin : (∫⁻ t : ℝ, ENNReal.ofReal (f t) ∂dualTime) =
      ENNReal.ofReal (∑' n : ℕ, q n) := by
    calc
      _ = ∫⁻ t : ℝ, ∑' n : ℕ, ENNReal.ofReal (F n t) ∂dualTime := by
        apply lintegral_congr_ae
        filter_upwards [hpoint] with t ht
        rw [← ht.tsum_eq]
        exact ENNReal.ofReal_tsum_of_nonneg (fun n => hFp n t) ht.summable
      _ = ∑' n : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal (F n t) ∂dualTime :=
        lintegral_tsum (fun n => (ENNReal.measurable_ofReal.comp (hFm n)).aemeasurable)
      _ = ∑' n : ℕ, ENNReal.ofReal (q n) := by
        apply tsum_congr
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hFi n)
          (Eventually.of_forall (hFp n)), hFq n]
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg hqp hqs).symm
  have hi : Integrable f dualTime := by
    refine ⟨hfm, (hasFiniteIntegral_iff_ofReal hfp).2 ?_⟩
    rw [hLin]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  have h := (ofReal_integral_eq_lintegral_ofReal hi hfp).trans hLin
  have hReal := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae hfp),
    ENNReal.toReal_ofReal (tsum_nonneg hqp)] using hReal

private theorem dual_time00_domain_series :
    Integrable dualTimeDensity00 dualTime ∧
      (∫ t : ℝ, dualTimeDensity00 t ∂dualTime) =
        ∑' n : ℕ, dualCoefficient00 n := by
  apply dual_positive_series_domain_integral dualLayer00 dualTimeDensity00 dualCoefficient00
    (fun n => by unfold dualLayer00; fun_prop)
    (fun n t => by unfold dualLayer00; positivity)
    (fun n => (dual_layer00_domain_integral n).1)
    (fun n => (dual_layer00_domain_integral n).2)
    dual_coefficient00_summable
    (by
      apply Measurable.aestronglyMeasurable
      unfold dualTimeDensity00
      fun_prop)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hden : 0 < Real.exp (6 * t) - 1 := by
      have : 1 < Real.exp (6 * t) := by rw [Real.one_lt_exp_iff]; positivity
      linarith
    unfold dualTimeDensity00
    positivity
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    change 0 < t at ht
    exact dual_layer00_positive_series ht

private theorem dual_time11_domain_series :
    Integrable dualTimeDensity11 dualTime ∧
      (∫ t : ℝ, dualTimeDensity11 t ∂dualTime) =
        ∑' n : ℕ, dualCoefficient11 n := by
  apply dual_positive_series_domain_integral dualLayer11 dualTimeDensity11 dualCoefficient11
    (fun n => by unfold dualLayer11; fun_prop)
    (fun n t => by unfold dualLayer11; positivity)
    (fun n => (dual_layer11_domain_integral n).1)
    (fun n => (dual_layer11_domain_integral n).2)
    dual_coefficient11_summable
    (by
      apply Measurable.aestronglyMeasurable
      unfold dualTimeDensity11
      fun_prop)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hden : 0 < Real.exp (6 * t) - 1 := by
      have : 1 < Real.exp (6 * t) := by rw [Real.one_lt_exp_iff]; positivity
      linarith
    unfold dualTimeDensity11
    positivity
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    change 0 < t at ht
    exact dual_layer11_positive_series ht

private theorem dual_log_coordinate00 (t : ℝ) :
    Real.exp t * dualDensity00 (Real.exp t) = dualTimeDensity00 t := by
  have hp : (Real.exp t) ^ (5 / 4 : ℝ) = Real.exp ((5 / 4 : ℝ) * t) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have h6 : (Real.exp t) ^ (6 : ℕ) = Real.exp (6 * t) := by
    rw [← Real.exp_nat_mul]
    norm_num
  unfold dualDensity00 dualTimeDensity00
  rw [hp, h6]
  ring

private theorem dual_log_coordinate11 (t : ℝ) :
    Real.exp t * dualDensity11 (Real.exp t) = dualTimeDensity11 t := by
  have h6 : (Real.exp t) ^ (6 : ℕ) = Real.exp (6 * t) := by
    rw [← Real.exp_nat_mul]
    norm_num
  unfold dualDensity11 dualTimeDensity11
  rw [Real.log_exp, h6]
  ring

/- These actual Ioi 1 domains and integrals are the suppliers consumed
by the original physical weighted Cauchy--Schwarz estimates. -/
private theorem actual_mean_zero_weighted_dual_domains_and_bounds :
    IntegrableOn dualDensity00 (Ioi 1) ∧
      IntegrableOn dualDensity11 (Ioi 1) ∧
      (∫ s : ℝ in Ioi 1, dualDensity00 s) = (∑' n : ℕ, dualCoefficient00 n) ∧
      (∫ s : ℝ in Ioi 1, dualDensity11 s) = (∑' n : ℕ, dualCoefficient11 n) ∧
      (∫ s : ℝ in Ioi 1, dualDensity00 s) ≤ 3 / 40 ∧
      (∫ s : ℝ in Ioi 1, dualDensity11 s) ≤ 3 / 160 := by
  have h00i : IntegrableOn dualDensity00 (Ioi 1) := by
    have ht : IntegrableOn (fun t : ℝ => Real.exp t • dualDensity00 (Real.exp t))
        (Ioi 0) := by
      apply dual_time00_domain_series.1.congr
      exact Eventually.of_forall fun t => by simpa only [smul_eq_mul] using
        (dual_log_coordinate00 t).symm
    simpa only [Real.exp_zero] using (integrableOn_comp_exp_Ioi dualDensity00 0).1 ht
  have h11i : IntegrableOn dualDensity11 (Ioi 1) := by
    have ht : IntegrableOn (fun t : ℝ => Real.exp t • dualDensity11 (Real.exp t))
        (Ioi 0) := by
      apply dual_time11_domain_series.1.congr
      exact Eventually.of_forall fun t => by simpa only [smul_eq_mul] using
        (dual_log_coordinate11 t).symm
    simpa only [Real.exp_zero] using (integrableOn_comp_exp_Ioi dualDensity11 0).1 ht
  have h00eq : (∫ s : ℝ in Ioi 1, dualDensity00 s) =
      ∫ t : ℝ, dualTimeDensity00 t ∂dualTime := by
    calc
      _ = ∫ t : ℝ in Ioi 0, Real.exp t • dualDensity00 (Real.exp t) := by
        simpa only [Real.exp_zero] using (integral_comp_exp_Ioi dualDensity00 0).symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun t => by
        simpa only [smul_eq_mul] using dual_log_coordinate00 t)
  have h11eq : (∫ s : ℝ in Ioi 1, dualDensity11 s) =
      ∫ t : ℝ, dualTimeDensity11 t ∂dualTime := by
    calc
      _ = ∫ t : ℝ in Ioi 0, Real.exp t • dualDensity11 (Real.exp t) := by
        simpa only [Real.exp_zero] using (integral_comp_exp_Ioi dualDensity11 0).symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun t => by
        simpa only [smul_eq_mul] using dual_log_coordinate11 t)
  rw [h00eq, h11eq, dual_time00_domain_series.2, dual_time11_domain_series.2]
  exact ⟨h00i, h11i, rfl, rfl,
    dual_coefficient00_series_bound, dual_coefficient11_series_bound⟩


private def originalGammaExcess (F : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ in Ioi Real.pi, ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖F x‖ ^ 2

private theorem original_gamma_excess_nonneg (F : ℝ → ℂ) :
    0 ≤ originalGammaExcess F := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpi : 1 ≤ x / Real.pi :=
    (le_div_iff₀ Real.pi_pos).2 (by
      have hx' : Real.pi < x := hx
      linarith)
  exact mul_nonneg (sub_nonneg.2 (one_le_pow₀ hxpi)) (sq_nonneg _)


private def originalPhysicalExcessWeight (x : ℝ) : ℝ :=
  (x / Real.pi) ^ (6 : ℕ) - 1

private theorem original_physical_excess_weight_pos {x : ℝ} (hx : Real.pi < x) :
    0 < originalPhysicalExcessWeight x := by
  have h : 1 < x / Real.pi := (lt_div_iff₀ Real.pi_pos).2 (by simpa using hx)
  have hp : (1 : ℝ) ^ (6 : ℕ) < (x / Real.pi) ^ (6 : ℕ) := by gcongr
  simpa only [originalPhysicalExcessWeight, one_pow] using sub_pos.mpr hp

private def originalPhysicalTraceKernel (x : ℝ) : ℝ :=
  x ^ (5 / 4 : ℝ) - Real.pi ^ (5 / 4 : ℝ)

private def originalPhysicalLogKernel (x : ℝ) : ℝ := Real.log (x / Real.pi)

private def originalPhysicalDual00 (x : ℝ) : ℝ :=
  originalPhysicalTraceKernel x ^ 2 / originalPhysicalExcessWeight x

private def originalPhysicalDual11 (x : ℝ) : ℝ :=
  originalPhysicalLogKernel x ^ 2 / originalPhysicalExcessWeight x

private theorem original_pi_five_halves_square :
    (Real.pi ^ (5 / 4 : ℝ)) ^ 2 = Real.pi ^ (5 / 2 : ℝ) := by
  rw [← Real.rpow_two, ← Real.rpow_mul Real.pi_pos.le]
  norm_num

private theorem original_pi_five_halves_jacobian :
    Real.pi * Real.pi ^ (5 / 2 : ℝ) = Real.pi ^ (7 / 2 : ℝ) := by
  calc
    _ = Real.pi ^ (1 : ℝ) * Real.pi ^ (5 / 2 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add Real.pi_pos]; norm_num

private theorem original_physical_dual00_scale {s : ℝ} (hs : 1 < s) :
    originalPhysicalDual00 (Real.pi * s) =
      Real.pi ^ (5 / 2 : ℝ) * dualDensity00 s := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hRatio : Real.pi * s / Real.pi = s := by field_simp [Real.pi_ne_zero]
  unfold originalPhysicalDual00 originalPhysicalTraceKernel originalPhysicalExcessWeight
    dualDensity00
  rw [hRatio, Real.mul_rpow Real.pi_pos.le hs0.le,
    ← original_pi_five_halves_square]
  ring

private theorem original_physical_dual11_scale (s : ℝ) :
    originalPhysicalDual11 (Real.pi * s) = dualDensity11 s := by
  have hRatio : Real.pi * s / Real.pi = s := by field_simp [Real.pi_ne_zero]
  simp only [originalPhysicalDual11, originalPhysicalLogKernel,
    originalPhysicalExcessWeight, dualDensity11, hRatio]

/- Actual domains and actual integrals, with the pi Jacobian paid.
The Ioi lower endpoint is retained throughout, rather than treated as a
pointwise inverse-square-root domain at x=pi. -/
private theorem original_physical_dual_domains_and_masses :
    IntegrableOn originalPhysicalDual00 (Ioi Real.pi) ∧
      IntegrableOn originalPhysicalDual11 (Ioi Real.pi) ∧
      (∫ x : ℝ in Ioi Real.pi, originalPhysicalDual00 x) =
        Real.pi ^ (7 / 2 : ℝ) * (∫ s : ℝ in Ioi 1, dualDensity00 s) ∧
      (∫ x : ℝ in Ioi Real.pi, originalPhysicalDual11 x) =
        Real.pi * (∫ s : ℝ in Ioi 1, dualDensity11 s) := by
  obtain ⟨h00, h11, _, _, _, _⟩ := actual_mean_zero_weighted_dual_domains_and_bounds
  have he00 : (fun s : ℝ => originalPhysicalDual00 (Real.pi * s)) =ᵐ[
      volume.restrict (Ioi (1 : ℝ))]
      (fun s : ℝ => Real.pi ^ (5 / 2 : ℝ) * dualDensity00 s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact original_physical_dual00_scale hs
  have he11 : (fun s : ℝ => originalPhysicalDual11 (Real.pi * s)) =ᵐ[
      volume.restrict (Ioi (1 : ℝ))] dualDensity11 :=
    Eventually.of_forall original_physical_dual11_scale
  have hc00 : IntegrableOn (fun s : ℝ => originalPhysicalDual00 (Real.pi * s))
      (Ioi (1 : ℝ)) := (h00.const_mul _).congr he00.symm
  have hc11 : IntegrableOn (fun s : ℝ => originalPhysicalDual11 (Real.pi * s))
      (Ioi (1 : ℝ)) := h11.congr he11.symm
  have hp00 : IntegrableOn originalPhysicalDual00 (Ioi Real.pi) := by
    simpa only [mul_one] using
      (integrableOn_Ioi_comp_mul_left_iff originalPhysicalDual00 1 Real.pi_pos).1 hc00
  have hp11 : IntegrableOn originalPhysicalDual11 (Ioi Real.pi) := by
    simpa only [mul_one] using
      (integrableOn_Ioi_comp_mul_left_iff originalPhysicalDual11 1 Real.pi_pos).1 hc11
  refine ⟨hp00, hp11, ?_, ?_⟩
  · calc
      _ = Real.pi * ∫ s : ℝ in Ioi 1, originalPhysicalDual00 (Real.pi * s) := by
        simpa only [mul_one, smul_eq_mul] using
          (integral_comp_mul_left_Ioi' originalPhysicalDual00 1 Real.pi_pos).symm
      _ = Real.pi * (Real.pi ^ (5 / 2 : ℝ) *
          (∫ s : ℝ in Ioi 1, dualDensity00 s)) := by
        rw [integral_congr_ae he00, integral_const_mul]
      _ = _ := by rw [← mul_assoc, original_pi_five_halves_jacobian]
  · calc
      _ = Real.pi * ∫ s : ℝ in Ioi 1, originalPhysicalDual11 (Real.pi * s) := by
        simpa only [mul_one, smul_eq_mul] using
          (integral_comp_mul_left_Ioi' originalPhysicalDual11 1 Real.pi_pos).symm
      _ = _ := by rw [integral_congr_ae he11]

/- The actual weighted CS mechanism. hk is only the actual dual-square
L1 domain; it is supplied by the preceding change of variables for each
concrete physical kernel. No CS estimate is an input. -/
private theorem original_physical_weighted_cs
    (U : ℝ → ℂ) (hU : originalPhysicalH6 U) (k : ℝ → ℝ)
    (hkm : Measurable k)
    (hk : IntegrableOn (fun x : ℝ => k x ^ 2 / originalPhysicalExcessWeight x)
      (Ioi Real.pi)) :
    IntegrableOn (fun x : ℝ => (k x : ℂ) * U x) (Ioi Real.pi) ∧
      ‖∫ x : ℝ in Ioi Real.pi, (k x : ℂ) * U x‖ ^ 2 ≤
        (∫ x : ℝ in Ioi Real.pi, k x ^ 2 / originalPhysicalExcessWeight x) *
          originalGammaExcess U := by
  let f : ℝ → ℂ := fun x => ((k x / Real.sqrt (originalPhysicalExcessWeight x) : ℝ) : ℂ)
  let g : ℝ → ℂ := fun x => ((Real.sqrt (originalPhysicalExcessWeight x) : ℝ) : ℂ) * U x
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Ioi Real.pi)) := by
    dsimp only [f]
    apply Measurable.aestronglyMeasurable
    exact Complex.continuous_ofReal.measurable.comp
      (hkm.div (by unfold originalPhysicalExcessWeight; fun_prop))
  have hgmeas : AEStronglyMeasurable g (volume.restrict (Ioi Real.pi)) := by
    exact ((show Continuous
      (fun x : ℝ => ((Real.sqrt (originalPhysicalExcessWeight x) : ℝ) : ℂ)) by
        unfold originalPhysicalExcessWeight
        fun_prop).aestronglyMeasurable).mul hU.1.aestronglyMeasurable
  have hfsq : (fun x : ℝ => ‖f x‖ ^ 2) =ᵐ[volume.restrict (Ioi Real.pi)]
      (fun x : ℝ => k x ^ 2 / originalPhysicalExcessWeight x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [f]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
      Real.sq_sqrt (original_physical_excess_weight_pos hx).le]
  have hgsq : (fun x : ℝ => ‖g x‖ ^ 2) =ᵐ[volume.restrict (Ioi Real.pi)]
      (fun x : ℝ => originalPhysicalExcessWeight x * ‖U x‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [g]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (original_physical_excess_weight_pos hx).le]
  have hfint : Integrable (fun x : ℝ => ‖f x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) := hk.congr hfsq.symm
  have hUint : Integrable
      (fun x : ℝ => originalPhysicalExcessWeight x * ‖U x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) := by
    have hs := (memLp_two_iff_integrable_sq_norm hU.1.aestronglyMeasurable).1 hU.1
    apply (hU.2.sub hs).congr
    exact Eventually.of_forall fun x => by
      dsimp [originalPhysicalExcessWeight]
      ring
  have hgint : Integrable (fun x : ℝ => ‖g x‖ ^ 2)
      (volume.restrict (Ioi Real.pi)) := hUint.congr hgsq.symm
  have hf : MemLp f 2 (volume.restrict (Ioi Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm hfmeas).2 hfint
  have hg : MemLp g 2 (volume.restrict (Ioi Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm hgmeas).2 hgint
  have hfg : (fun x : ℝ => f x * g x) =ᵐ[volume.restrict (Ioi Real.pi)]
      (fun x : ℝ => (k x : ℂ) * U x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hs : (Real.sqrt (originalPhysicalExcessWeight x) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.2 (original_physical_excess_weight_pos hx)).ne'
    dsimp [f, g]
    push_cast
    field_simp [hs]
    <;> ring
  have hProduct : IntegrableOn (fun x : ℝ => (k x : ℂ) * U x) (Ioi Real.pi) :=
    (hf.integrable_mul hg).congr hfg
  refine ⟨hProduct, ?_⟩
  have hnorm : ‖∫ x : ℝ in Ioi Real.pi, (k x : ℂ) * U x‖ ≤
      ∫ x : ℝ in Ioi Real.pi, ‖f x‖ * ‖g x‖ := by
    rw [← integral_congr_ae hfg]
    simpa only [norm_mul] using
      norm_integral_le_integral_norm (μ := volume.restrict (Ioi Real.pi))
        (fun x : ℝ => f x * g x)
  have hpq : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have hh := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume.restrict (Ioi Real.pi)) (f := f) (g := g)
      hpq (by simpa using hf) (by simpa using hg)
  simp_rw [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
  have hfmass : 0 ≤ ∫ x : ℝ in Ioi Real.pi, ‖f x‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hgmass : 0 ≤ ∫ x : ℝ in Ioi Real.pi, ‖g x‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ ≤ (Real.sqrt (∫ x : ℝ in Ioi Real.pi, ‖f x‖ ^ 2) *
        Real.sqrt (∫ x : ℝ in Ioi Real.pi, ‖g x‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hh) 2
    _ = (∫ x : ℝ in Ioi Real.pi, ‖f x‖ ^ 2) *
        (∫ x : ℝ in Ioi Real.pi, ‖g x‖ ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hfmass, Real.sq_sqrt hgmass]
    _ = _ := by rw [integral_congr_ae hfsq, integral_congr_ae hgsq]; rfl

/- The physical kernels have genuine L1 products and their two sharp
dual-integral bounds, before being identified with the actual moments. -/
private theorem original_physical_trace_log_product_domains_and_cs
    (U : ℝ → ℂ) (hU : originalPhysicalH6 U) :
    IntegrableOn (fun x : ℝ => (originalPhysicalTraceKernel x : ℂ) * U x)
      (Ioi Real.pi) ∧
      IntegrableOn (fun x : ℝ => (originalPhysicalLogKernel x : ℂ) * U x)
        (Ioi Real.pi) ∧
      ‖∫ x : ℝ in Ioi Real.pi, (originalPhysicalTraceKernel x : ℂ) * U x‖ ^ 2 ≤
        Real.pi ^ (7 / 2 : ℝ) * (∫ s : ℝ in Ioi 1, dualDensity00 s) * originalGammaExcess U ∧
      ‖∫ x : ℝ in Ioi Real.pi, (originalPhysicalLogKernel x : ℂ) * U x‖ ^ 2 ≤
        Real.pi * (∫ s : ℝ in Ioi 1, dualDensity11 s) * originalGammaExcess U := by
  obtain ⟨h00, h11, hm00, hm11⟩ := original_physical_dual_domains_and_masses
  have hT := original_physical_weighted_cs U hU originalPhysicalTraceKernel
    (by unfold originalPhysicalTraceKernel; fun_prop) h00
  have hL := original_physical_weighted_cs U hU originalPhysicalLogKernel
    (by unfold originalPhysicalLogKernel; fun_prop) h11
  refine ⟨hT.1, hL.1, ?_, ?_⟩
  · have hb :
        ‖∫ x : ℝ in Ioi Real.pi, (originalPhysicalTraceKernel x : ℂ) * U x‖ ^ 2 ≤
          (∫ x : ℝ in Ioi Real.pi, originalPhysicalDual00 x) * originalGammaExcess U := hT.2
    rw [hm00] at hb
    exact hb
  · have hb :
        ‖∫ x : ℝ in Ioi Real.pi, (originalPhysicalLogKernel x : ℂ) * U x‖ ^ 2 ≤
          (∫ x : ℝ in Ioi Real.pi, originalPhysicalDual11 x) * originalGammaExcess U := hL.2
    rw [hm11] at hb
    exact hb


/-- Actual physical moment domains and bounds on the original H6 space.
The same U supplies the weighted L2 factor and both literal products. -/
theorem actual_h6_weighted_physical_moments
    (U : ℝ → ℂ) (hU : originalPhysicalH6 U) :
    IntegrableOn (fun x : ℝ =>
      ((x ^ (5 / 4 : ℝ) - Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) * U x) (Ioi Real.pi) ∧
      IntegrableOn (fun x : ℝ => (Real.log (x / Real.pi) : ℂ) * U x) (Ioi Real.pi) ∧
      ‖∫ x : ℝ in Ioi Real.pi,
        ((x ^ (5 / 4 : ℝ) - Real.pi ^ (5 / 4 : ℝ) : ℝ) : ℂ) * U x‖ ^ 2 ≤
        (3 / 40 : ℝ) * Real.pi ^ (7 / 2 : ℝ) *
          (∫ x : ℝ in Ioi Real.pi, ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖U x‖ ^ 2) ∧
      ‖∫ x : ℝ in Ioi Real.pi, (Real.log (x / Real.pi) : ℂ) * U x‖ ^ 2 ≤
        (3 / 160 : ℝ) * Real.pi *
          (∫ x : ℝ in Ioi Real.pi, ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖U x‖ ^ 2) := by
  obtain ⟨hTp, hLp, hTc, hLc⟩ := original_physical_trace_log_product_domains_and_cs U hU
  obtain ⟨_, _, _, _, h00, h11⟩ := actual_mean_zero_weighted_dual_domains_and_bounds
  have hD := original_gamma_excess_nonneg U
  have hT : ‖∫ x : ℝ in Ioi Real.pi, (originalPhysicalTraceKernel x : ℂ) * U x‖ ^ 2 ≤
      (3 / 40 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * originalGammaExcess U := by
    calc
      _ ≤ Real.pi ^ (7 / 2 : ℝ) * (3 / 40 : ℝ) * originalGammaExcess U :=
        hTc.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h00 (by positivity)) hD)
      _ = _ := by ring
  have hL : ‖∫ x : ℝ in Ioi Real.pi, (originalPhysicalLogKernel x : ℂ) * U x‖ ^ 2 ≤
      (3 / 160 : ℝ) * Real.pi * originalGammaExcess U := by
    calc
      _ ≤ Real.pi * (3 / 160 : ℝ) * originalGammaExcess U :=
        hLc.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h11 Real.pi_pos.le) hD)
      _ = _ := by ring
  exact ⟨by simpa only [originalPhysicalTraceKernel] using hTp,
    by simpa only [originalPhysicalLogKernel] using hLp,
    by simpa only [originalPhysicalTraceKernel, originalGammaExcess] using hT,
    by simpa only [originalPhysicalLogKernel, originalGammaExcess] using hL⟩

end D5.S3.Weil.ZetaGamma.FormCore.SourceOriginalMeanZeroGamma

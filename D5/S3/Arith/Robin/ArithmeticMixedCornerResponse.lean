/- GID: D5/S3/Arith/Robin/ArithmeticMixedCornerResponse
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ArithmeticMixedCornerResponse
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual coprime corners have a positive integral and quantitative area bounds. -/

import D5.S3.Arith.Robin.ActualRobinClockCovariance
import D5.S3.Arith.Robin.LogLogHigherDerivative
import D5.S3.Arith.Robin.MellinWeightedVariation
import D5.S3.Arith.Robin.PrimeFiberPropagation

/-!
The arithmetic response uses the same base integer in all four corners.
Coprimality is required only between the two multipliers, not between either
multiplier and the base. The kernel is the existing activation density.
The double integral and its area bounds concern a finite response and do not
determine the absolute Robin sign.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Interval Topology
open Set MeasureTheory

namespace D5.S3.Arith.Robin.ArithmeticMixedCornerResponse

open D5.S3.Arith.Robin.ActualRobinClockCovariance
open D5.S3.Arith.Robin.PrimeFiberPropagation (divisorRatio divisorRatio_pos)

/-- The absolute logarithmic Robin margin, including Euler's constant. -/
def G (n : ℕ) : ℝ :=
  Real.log (divisorRatio n) - Real.eulerMascheroniConstant -
    Real.log (Real.log (Real.log (n : ℝ)))

private theorem density_pos {t : ℝ} (ht : 1 < t) : 0 < activationDensity t := by
  have h := D5.S3.Arith.Robin.LogLogHigherDerivative.positiveKernel_pos 1 0 0 ht
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hl0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have he : activationDensity t =
      D5.S3.Arith.Robin.LogLogHigherDerivative.positiveKernel 1 0 0 t := by
    norm_num [activationDensity, D5.S3.Arith.Robin.LogLogHigherDerivative.positiveKernel]
    field_simp [ht0, hl0]
  exact he.symm ▸ h

private theorem density_antitone {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    activationDensity t ≤ activationDensity s := by
  have ht := hs.trans_le hst
  have h := D5.S3.Arith.Robin.MellinWeightedVariation.scaleWeight_antitone
    (x := s) (y := 1) hs (by norm_num) (by linarith) hst (by simp)
  rw [D5.S3.Arith.Robin.MellinWeightedVariation.scaleWeight_eq,
    D5.S3.Arith.Robin.MellinWeightedVariation.scaleWeight_eq] at h
  simp only [mul_one] at h
  change t * activationDensity t ≤ s * activationDensity s at h
  nlinarith [mul_nonneg (sub_nonneg.mpr hst) (density_pos ht).le]

private theorem shifted_g_integrable {x a : ℝ} (hx : 1 < x) (ha : 0 ≤ a) :
    IntervalIntegrable (fun u => g (x + u)) volume 0 a := by
  have h := (price_terms_integrable hx (by linarith : x ≤ x + a)).2.comp_add_left x
  simpa only [sub_self, add_sub_cancel_left, g, one_div, mul_inv_rev,
    div_eq_mul_inv, mul_comm, one_mul] using h

private theorem shifted_density_integrable {x a : ℝ} (hx : 1 < x) (ha : 0 ≤ a) :
    IntervalIntegrable (fun u => activationDensity (x + u)) volume 0 a := by
  simpa only [sub_self, add_sub_cancel_left] using
    (density_integrable hx (by linarith : x ≤ x + a)).comp_add_left x

private theorem shifted_g_integral {x a : ℝ} (hx : 1 < x) (ha : 0 ≤ a) :
    (∫ u in 0..a, g (x + u)) =
      Real.log (Real.log (x + a)) - Real.log (Real.log x) := by
  rw [intervalIntegral.integral_comp_add_left]
  simp only [add_zero]
  simpa only [g, one_div, mul_inv_rev, div_eq_mul_inv, mul_comm, one_mul] using
    integral_inv_div_log hx (by linarith : 1 < x + a)

private theorem shifted_density_integral {x b : ℝ} (hx : 1 < x) (hb : 0 ≤ b) :
    (∫ v in 0..b, activationDensity (x + v)) = g x - g (x + b) := by
  rw [intervalIntegral.integral_comp_add_left]
  simpa only [add_zero] using density_integral hx (by linarith : x ≤ x + b)

private theorem rectangle {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 0 < b) :
    let J := Real.log (Real.log (x + a)) + Real.log (Real.log (x + b)) -
      Real.log (Real.log x) - Real.log (Real.log (x + a + b))
    J = (∫ u in 0..a, ∫ v in 0..b, activationDensity (x + u + v)) ∧
    0 < J ∧ a * b * activationDensity (x + a + b) ≤ J ∧
      J ≤ a * b * activationDensity x := by
  dsimp only
  let H := fun u : ℝ => ∫ v in 0..b, activationDensity (x + u + v)
  have hH : ∀ u ∈ Icc 0 a, H u = g (x + u) - g (x + b + u) := by
    intro u hu
    have hi := shifted_density_integral (by linarith [hu.1] : 1 < x + u) hb.le
    simpa only [H, add_right_comm x u b] using hi
  have hgi := shifted_g_integrable hx ha.le
  have hgj := shifted_g_integrable (by linarith : 1 < x + b) ha.le
  have hHi : IntervalIntegrable H volume 0 a := by
    apply (hgi.sub hgj).congr
    intro u hu
    rw [uIoc_of_le ha.le] at hu
    exact (hH u ⟨hu.1.le, hu.2⟩).symm
  have heq : (∫ u in 0..a, H u) =
      Real.log (Real.log (x + a)) + Real.log (Real.log (x + b)) -
        Real.log (Real.log x) - Real.log (Real.log (x + a + b)) := by
    calc
      _ = ∫ u in 0..a, g (x + u) - g (x + b + u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le ha.le] at hu
        exact hH u hu
      _ = _ := by
        rw [intervalIntegral.integral_sub hgi hgj,
          shifted_g_integral hx ha.le,
          shifted_g_integral (by linarith : 1 < x + b) ha.le]
        rw [add_right_comm x b a]
        ring
  have hlower : a * b * activationDensity (x + a + b) ≤ ∫ u in 0..a, H u := by
    calc
      _ = ∫ _ in 0..a, b * activationDensity (x + a + b) := by
        simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on ha.le intervalIntegrable_const hHi
        intro u hu
        calc
          _ = ∫ _ in 0..b, activationDensity (x + a + b) := by
            simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
          _ ≤ H u := by
            apply intervalIntegral.integral_mono_on hb.le intervalIntegrable_const
              (shifted_density_integrable (by linarith [hu.1]) hb.le)
            intro v hv
            exact density_antitone (by linarith [hu.1, hv.1])
              (by linarith [hu.2, hv.2])
  have hupper : (∫ u in 0..a, H u) ≤ a * b * activationDensity x := by
    calc
      _ ≤ ∫ _ in 0..a, b * activationDensity x := by
        apply intervalIntegral.integral_mono_on ha.le hHi intervalIntegrable_const
        intro u hu
        calc
          H u ≤ ∫ _ in 0..b, activationDensity x := by
            apply intervalIntegral.integral_mono_on hb.le
              (shifted_density_integrable (by linarith [hu.1]) hb.le) intervalIntegrable_const
            intro v hv
            exact density_antitone hx (by linarith [hu.1, hv.1])
          _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring
  refine ⟨heq.symm, ?_, ?_, ?_⟩
  · exact (mul_pos (mul_pos ha hb) (density_pos (by linarith))).trans_le (heq ▸ hlower)
  · exact heq ▸ hlower
  · exact heq ▸ hupper

private theorem log_ratio_cancellation {n r s : ℕ} (hn : 0 < n)
    (hr : 0 < r) (hs : 0 < s) (hrs : Nat.Coprime r s) :
    Real.log (divisorRatio (n * r * s)) + Real.log (divisorRatio n) =
      Real.log (divisorRatio (n * r)) + Real.log (divisorRatio (n * s)) := by
  have hg : Nat.gcd (n * r) (n * s) = n := by
    rw [Nat.gcd_mul_left, hrs.gcd_eq_one, mul_one]
  have hl : Nat.lcm (n * r) (n * s) = n * r * s := by
    apply Nat.eq_of_mul_eq_mul_left hn
    calc
      n * Nat.lcm (n * r) (n * s) = (n * r) * (n * s) := by
        calc
          _ = Nat.gcd (n * r) (n * s) * Nat.lcm (n * r) (n * s) := by rw [hg]
          _ = _ := Nat.gcd_mul_lcm (n * r) (n * s)
      _ = n * (n * r * s) := by ring
  have hσ := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).lcm_apply_mul_gcd_apply
    (x := n * r) (y := n * s)
  rw [hg, hl] at hσ
  have hσR : (ArithmeticFunction.sigma 1 (n * r * s) : ℝ) *
      (ArithmeticFunction.sigma 1 n : ℝ) =
      (ArithmeticFunction.sigma 1 (n * r) : ℝ) *
        (ArithmeticFunction.sigma 1 (n * s) : ℝ) := by exact_mod_cast hσ
  have hpos : ∀ m : ℕ, 0 < m → 0 < divisorRatio m :=
    fun _ hm => divisorRatio_pos hm.ne'
  rw [← Real.log_mul (hpos _ (by positivity)).ne' (hpos _ hn).ne',
    ← Real.log_mul (hpos _ (by positivity)).ne' (hpos _ (by positivity)).ne']
  apply congrArg Real.log
  unfold divisorRatio
  push_cast
  rw [div_mul_div_comm, div_mul_div_comm, hσR]
  congr 1
  ring

/-- The actual arithmetic mixed response, its exact repeated-FTC formula and
quantitative curvature bounds. No coprimality with `n` is required. -/
theorem arithmetic_mixed_response {n r s : ℕ} (hn : 3 ≤ n)
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hrs : Nat.Coprime r s) :
    let x := Real.log (n : ℝ)
    let a := Real.log (r : ℝ)
    let b := Real.log (s : ℝ)
    let J := G (n * r * s) + G n - G (n * r) - G (n * s)
    1 < x ∧ 0 < a ∧ 0 < b ∧
    J = (∫ u in 0..a, ∫ v in 0..b, activationDensity (x + u + v)) ∧
    0 < J ∧ a * b * activationDensity (x + a + b) ≤ J ∧
      J ≤ a * b * activationDensity x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hx : 1 < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hn0).mpr
      (Real.exp_one_lt_three.trans_le (by exact_mod_cast hn))
  have ha : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hb : 0 < Real.log (s : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < s))
  have hnr : Real.log (n * r : ℕ) = Real.log (n : ℝ) + Real.log (r : ℝ) := by
    push_cast
    exact Real.log_mul hn0.ne' hr0.ne'
  have hns : Real.log (n * s : ℕ) = Real.log (n : ℝ) + Real.log (s : ℝ) := by
    push_cast
    exact Real.log_mul hn0.ne' hs0.ne'
  have hnrs : Real.log (n * r * s : ℕ) =
      Real.log (n : ℝ) + Real.log (r : ℝ) + Real.log (s : ℝ) := by
    push_cast
    rw [Real.log_mul (mul_pos hn0 hr0).ne' hs0.ne', Real.log_mul hn0.ne' hr0.ne']
  have hc := log_ratio_cancellation (by omega : 0 < n) (by omega : 0 < r)
    (by omega : 0 < s) hrs
  have hJ : G (n * r * s) + G n - G (n * r) - G (n * s) =
      Real.log (Real.log (Real.log (n : ℝ) + Real.log (r : ℝ))) +
      Real.log (Real.log (Real.log (n : ℝ) + Real.log (s : ℝ))) -
      Real.log (Real.log (Real.log (n : ℝ))) -
      Real.log (Real.log (Real.log (n : ℝ) + Real.log (r : ℝ) + Real.log (s : ℝ))) := by
    unfold G
    rw [hnr, hns, hnrs]
    linarith
  dsimp only
  rw [hJ]
  exact ⟨hx, ha, hb, rectangle hx ha hb⟩


end D5.S3.Arith.Robin.ArithmeticMixedCornerResponse

#print axioms D5.S3.Arith.Robin.ArithmeticMixedCornerResponse.arithmetic_mixed_response

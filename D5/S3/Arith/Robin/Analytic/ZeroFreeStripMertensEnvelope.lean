/- GID: D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full actual zero strip gives the critical arithmetic B power envelope. -/
/- Copyright 2026 The Omega Institute
   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
       http://www.apache.org/licenses/LICENSE-2.0
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License. -/

import D5.S3.Weil.Mertens.ZeroAbscissaPower
import D5.S3.Weil.Mertens.IntegratedExplicit.WholeFormula
import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
import D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability
import D5.S3.Arith.Robin.EulerLayerRootCorrection
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! The classical integrated explicit formula, Abel summation and the quadratic
logarithmic remainder give an arithmetic estimate for the canonical B.
The complete actual occurrence series retains analytic multiplicities.
The positive W-tail majorant retains the critical logarithmic denominator.
The nonlinear term uses the weaker exponent 1-alpha/2 from the actual zero
abscissa and the unconditional prime number limits.

The Mertens supplier retains the PrimeNumberTheoremAnd contributors'
Apache-2.0 notice, its IEANTN/Mertens.lean source at commit
6a380f0c4658c04a420a9eb00b1ed62a1e3fde01, and the attribution to
Leo Goldmakher, A quick proof of Mertens' theorem. Its notice and license
remain at Library/notes/pntplus2026mertens.md in the supplying repository.
This is a conditional estimate and makes no assertion of RH or literature
priority. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent (W R)
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U psiErrorKernel)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
  (B w Jpsi S N weighted_eq tails finite_cancellation)

namespace D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope

private def coeffMass : ℝ := ∑' k : ℕ, ‖actualCoeff k‖

private lemma actualH_strip {alpha y : ℝ} (hy : 0 ≤ y)
    (hstrip : ∀ rho : ℂ, IsNontrivialZero rho → rho.re ≤ 1 - alpha) :
    ‖actualH y‖ ≤ coeffMass * Real.exp ((1 - alpha) * y) := by
  have hterm (k : ℕ) :
      ‖actualCoeff k * Complex.exp ((y : ℂ) * actualZero k)‖ ≤
        ‖actualCoeff k‖ * Real.exp ((1 - alpha) * y) := by
    have hz : (actualZero k).re ≤ 1 - alpha :=
      hstrip (actualZero k) (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hz hy
  have hmajor := actualCoeff_hasSum.summable.norm.hasSum.mul_right
    (Real.exp ((1 - alpha) * y))
  -- Use the actual series, whose summability is independently public.
  exact (actualH_summable y).hasSum.norm_le_of_bounded hmajor hterm

private lemma Q_exp_bound {alpha : ℝ} (hhalf : alpha ≤ 1 / 2)
    (hstrip : ∀ rho : ℂ, IsNontrivialZero rho → rho.re ≤ 1 - alpha) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, Real.log 2 ≤ y →
      |Q (Real.exp y)| ≤ C * Real.exp (-alpha * y) := by
  let c : ℝ := |Real.log (2 * Real.pi)| + |1 - Real.log 2|
  let C : ℝ := coeffMass + c
  have hm : 0 ≤ coeffMass := tsum_nonneg (fun _ => norm_nonneg _)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  apply Exists.intro C
  apply And.intro (add_nonneg hm hc)
  intro y hy
  have hy0 : 0 < y := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hy
  have hexp2 : 2 ≤ Real.exp y := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hy
  have hformula := congrArg Complex.re (actual_integrated_explicit_formula hy0)
  simp only [Complex.ofReal_re] at hformula
  have hU : U (Real.exp y) =
      (actualH y).re + Real.log (2 * Real.pi) - trivialT y := by linarith
  have htriv : |trivialT y| ≤ |1 - Real.log 2| := by
    rw [abs_of_nonneg (trivialT_nonneg hy0.le)]
    exact (trivialT_le_mass hy0.le).trans (le_abs_self _)
  have he : 1 ≤ Real.exp ((1 - alpha) * y) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hy0.le)
  have hb : |U (Real.exp y)| ≤ C * Real.exp ((1 - alpha) * y) := by
    rw [hU]
    calc
      _ ≤ |(actualH y).re + Real.log (2 * Real.pi)| + |trivialT y| := abs_sub _ _
      _ ≤ (|(actualH y).re| + |Real.log (2 * Real.pi)|) + |trivialT y| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ coeffMass * Real.exp ((1 - alpha) * y) + c := by
        dsimp [c]
        linarith [(Complex.abs_re_le_norm (actualH y)).trans (actualH_strip hy0.le hstrip)]
      _ ≤ (coeffMass + c) * Real.exp ((1 - alpha) * y) := by
        nlinarith [mul_le_mul_of_nonneg_left he hc]
      _ = _ := rfl
  have hQid : Q (Real.exp y) = -U (Real.exp y) / Real.exp y := by
    have hp := D5.S3.Weil.Mertens.ZeroAbscissaPower.primitive_eq_negative_tail hexp2
    simpa only [neg_div, neg_neg] using (congrArg (fun z : ℝ => -z) hp).symm
  rw [hQid, abs_div, abs_neg, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (C * Real.exp ((1 - alpha) * y)) / Real.exp y :=
      div_le_div_of_nonneg_right hb (Real.exp_nonneg _)
    _ = C * Real.exp (-alpha * y) := by
      rw [mul_div_assoc, ← Real.exp_sub]
      congr 2
      ring

private lemma Jpsi_exp_bound {alpha C y : ℝ} (ha : 0 < alpha) (hC : 0 ≤ C)
    (hQ : ∀ v : ℝ, Real.log 2 ≤ v → |Q (Real.exp v)| ≤ C * Real.exp (-alpha * v))
    (hyl : Real.log 2 ≤ y) (hy1 : 1 ≤ y) :
    |Jpsi (Real.exp y)| ≤ 4 * C * Real.exp (-alpha * y) / y := by
  have hy0 : 0 < y := by linarith
  have hexp2 : 2 ≤ Real.exp y := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hyl
  let Ttail : ℝ := ∫ v in Ioi y, W v * Q (Real.exp v)
  have htr := D5.S3.Weil.Mertens.WeightedTailTransport.transport_exp hyl
    (D5.S3.Arith.Robin.CompleteMertensPeak.complete_mertens_ledger hexp2).1
  have hint : IntegrableOn (fun v : ℝ => W v * Q (Real.exp v)) (Ioi y) := htr.1
  have hmajor : IntegrableOn (fun v : ℝ => (C * Real.exp (-alpha * y)) * W v) (Ioi y) :=
    (CountableResolvent.W_tail_integrable hy0).const_mul _
  have hT : |Ttail| ≤ C * Real.exp (-alpha * y) * R y := by
    calc
      _ ≤ ∫ v in Ioi y, |W v * Q (Real.exp v)| := abs_integral_le_integral_abs
      _ ≤ ∫ v in Ioi y, (C * Real.exp (-alpha * y)) * W v := by
        apply setIntegral_mono_on hint.abs hmajor measurableSet_Ioi
        intro v hv
        have hw := CountableResolvent.W_nonneg (hy0.le.trans hv.le)
        have he : Real.exp (-alpha * v) ≤ Real.exp (-alpha * y) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left hv.le (neg_nonpos.mpr ha.le)
        rw [abs_mul, abs_of_nonneg hw]
        calc
          _ ≤ W v * (C * Real.exp (-alpha * v)) :=
            mul_le_mul_of_nonneg_left (hQ v (hyl.trans hv.le)) hw
          _ ≤ W v * (C * Real.exp (-alpha * y)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hC) hw
          _ = _ := by ring
      _ = C * Real.exp (-alpha * y) * R y := by
        rw [integral_const_mul, CountableResolvent.W_tail hy0]
  have hwJ : D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail psiErrorKernel
      (Real.exp y) = Jpsi (Real.exp y) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact weighted_eq t
  have hR : 0 < R y := by dsimp [R]; positivity
  have ht := htr.2
  change R y * (Q (Real.exp y) -
    D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail psiErrorKernel (Real.exp y) /
      D5.S3.Weil.Mertens.WeightedTailTransport.r (Real.exp y)) = Ttail at ht
  rw [hwJ, D5.S3.Weil.Mertens.WeightedTailTransport.r_exp y] at ht
  have hid : Jpsi (Real.exp y) = R y * Q (Real.exp y) - Ttail := by
    have hh : R y * Q (Real.exp y) - Jpsi (Real.exp y) = Ttail := by
      calc
        _ = R y * (Q (Real.exp y) - Jpsi (Real.exp y) / R y) := by field_simp [hR.ne']
        _ = Ttail := ht
    linarith
  have hRy : R y ≤ 2 / y := by
    dsimp [R]
    apply (div_le_div_iff₀ (sq_pos_of_pos hy0) hy0).mpr
    nlinarith [mul_nonneg hy0.le (sub_nonneg.mpr hy1)]
  rw [hid]
  calc
    _ ≤ |R y * Q (Real.exp y)| + |Ttail| := abs_sub _ _
    _ = R y * |Q (Real.exp y)| + |Ttail| := by rw [abs_mul, abs_of_pos hR]
    _ ≤ R y * (C * Real.exp (-alpha * y)) + C * Real.exp (-alpha * y) * R y :=
      add_le_add (mul_le_mul_of_nonneg_left (hQ y hyl) hR.le) hT
    _ = (2 * C * Real.exp (-alpha * y)) * R y := by ring
    _ ≤ (2 * C * Real.exp (-alpha * y)) * (2 / y) :=
      mul_le_mul_of_nonneg_left hRy (by positivity)
    _ = _ := by ring

private lemma Jpsi_bound {alpha C x : ℝ} (ha : 0 < alpha) (hC : 0 ≤ C)
    (hQ : ∀ y : ℝ, Real.log 2 ≤ y → |Q (Real.exp y)| ≤ C * Real.exp (-alpha * y))
    (hx2 : 2 ≤ x) (hxe : Real.exp 1 ≤ x) :
    |Jpsi x| ≤ (4 * C) / (x ^ alpha * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hyl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
  have hy1 : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxe
  have hh := Jpsi_exp_bound ha hC hQ hyl hy1
  rw [Real.exp_log hx0] at hh
  have he : Real.exp (-alpha * Real.log x) = (x ^ alpha)⁻¹ := by
    rw [Real.rpow_def_of_pos hx0, ← Real.exp_neg]
    congr 1
    ring
  rw [he] at hh
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hh

private lemma S_bound {alpha H x : ℝ} (hhalf : alpha ≤ 1 / 2)
    (hgap : ∀ t : ℝ, Chebyshev.psi t - Chebyshev.theta t ≤ H * Real.sqrt t)
    (hx2 : 2 ≤ x) (hxe : Real.exp 1 ≤ x) :
    |S x| ≤ (4 * |H|) / (x ^ alpha * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hxe
  have hL0 : 0 < Real.log x := by linarith
  have hi := (tails hx2).2.1
  have hA := D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.A_data
    (show 1 < x by linarith)
  have hiA := hA.1
  change IntegrableOn (fun t : ℝ => Real.sqrt t * w t) (Ioi x) at hiA
  have hAupper := hA.2.2
  change (∫ t in Ioi x, Real.sqrt t * w t) ≤
    2 / (Real.sqrt x * Real.log x) at hAupper
  have hmajor : IntegrableOn (fun t : ℝ => |H| * (Real.sqrt t * w t)) (Ioi x) :=
    hiA.const_mul _
  have hS : |S x| ≤ (4 * |H|) / (x ^ (1 / 2 : ℝ) * Real.log x) := by
    calc
      _ ≤ ∫ t in Ioi x, |(Chebyshev.psi t - Chebyshev.theta t) * w t| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioi x, |H| * (Real.sqrt t * w t) := by
        apply setIntegral_mono_on hi.abs hmajor measurableSet_Ioi
        intro t ht
        have hw := D5.S3.Arith.Robin.MellinWeightedVariation.weight_nonneg
          ((show 1 < x by linarith).trans ht)
        change 0 ≤ w t at hw
        have hgap' : |Chebyshev.psi t - Chebyshev.theta t| ≤ |H| * Real.sqrt t := by
          rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t))]
          exact (hgap t).trans (mul_le_mul_of_nonneg_right (le_abs_self H) (Real.sqrt_nonneg _))
        rw [abs_mul, abs_of_nonneg hw]
        calc
          _ ≤ (|H| * Real.sqrt t) * w t := mul_le_mul_of_nonneg_right hgap' hw
          _ = |H| * (Real.sqrt t * w t) := by ring
      _ = |H| * (∫ t in Ioi x, Real.sqrt t * w t) := by rw [integral_const_mul]
      _ ≤ |H| * (2 / (Real.sqrt x * Real.log x)) :=
        mul_le_mul_of_nonneg_left hAupper (abs_nonneg _)
      _ = (2 * |H|) / (x ^ (1 / 2 : ℝ) * Real.log x) := by
        rw [Real.sqrt_eq_rpow]
        ring
      _ ≤ (4 * |H|) / (x ^ (1 / 2 : ℝ) * Real.log x) :=
        div_le_div_of_nonneg_right (by nlinarith [abs_nonneg H]) (by positivity)
  exact hS.trans (div_le_div_of_nonneg_left (by positivity)
    (mul_pos (Real.rpow_pos_of_pos hx0 _) hL0)
    (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1 hhalf) hL0.le))

lemma theta_power_bound {β C X : ℝ} (hβ : (1 / 2 : ℝ) < β)
    (hpsi : ∀ x : ℝ, X ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ β) :
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧
      ∀ x : ℝ, R ≤ x → |Chebyshev.theta x - x| ≤ K * x ^ β := by
  obtain ⟨H, hH⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  apply Exists.intro (|C| + |H|)
  apply Exists.intro (max 2 X)
  apply And.intro (add_nonneg (abs_nonneg C) (abs_nonneg H))
  apply And.intro (le_max_left _ _)
  intro x hx
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hp : 0 ≤ x ^ β := Real.rpow_nonneg hx0.le _
  have hs : Real.sqrt x ≤ x ^ β := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 hβ.le
  have hgap : |Chebyshev.psi x - Chebyshev.theta x| ≤ |H| * x ^ β := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))]
    calc
      _ ≤ H * Real.sqrt x := hH x
      _ ≤ |H| * Real.sqrt x :=
        mul_le_mul_of_nonneg_right (le_abs_self H) (Real.sqrt_nonneg _)
      _ ≤ |H| * x ^ β := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  calc
    |Chebyshev.theta x - x| =
        |(Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x)| := by
      congr 1
      ring
    _ ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := abs_sub _ _
    _ ≤ C * x ^ β + |H| * x ^ β :=
      add_le_add (hpsi x ((le_max_right _ _).trans hx)) hgap
    _ ≤ |C| * x ^ β + |H| * x ^ β :=
      add_le_add (mul_le_mul_of_nonneg_right (le_abs_self C) hp) le_rfl
    _ = (|C| + |H|) * x ^ β := by ring

private lemma strip_theta_rate {alpha : ℝ} (ha : 0 < alpha) (hhalf : alpha ≤ 1 / 2)
    (hstrip : ∀ rho : ℂ, IsNontrivialZero rho → rho.re ≤ 1 - alpha) :
    ∃ K R : ℝ, 0 ≤ K ∧ 2 ≤ R ∧ ∀ x : ℝ, R ≤ x →
      |Chebyshev.theta x - x| ≤ K * x ^ (1 - alpha / 2) := by
  classical
  have hTheta : zeroAbscissa ≤ 1 - alpha := by
    apply csSup_le (show (Complex.re '' {rho : ℂ | IsNontrivialZero rho}).Nonempty from
      ⟨(actualZero 0).re, actualZero 0,
        actualData.zero_isNontrivial (actualOccurrenceEquiv 0).1, rfl⟩)
    rintro r ⟨rho, hrho, rfl⟩
    exact hstrip rho hrho
  let beta : ℝ := 1 - alpha / 2
  have hepsilon : 0 < beta - zeroAbscissa := by dsimp [beta]; linarith
  obtain ⟨C, hpsi⟩ := D5.S3.Weil.Mertens.ZeroAbscissaPower.actual_zero_abscissa_power_bound
    (beta - zeroAbscissa) hepsilon
  have hpsi' : ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ beta := by
    simpa only [show zeroAbscissa + (beta - zeroAbscissa) = beta by ring] using hpsi
  have hbeta : (1 / 2 : ℝ) < beta := by dsimp [beta]; linarith
  exact theta_power_bound hbeta hpsi'

lemma nonlinear_quadratic {x : ℝ} (hx : Real.exp 2 ≤ x)
    (htheta : x / 2 ≤ Chebyshev.theta x) :
    |N x| ≤ 8 * ((Chebyshev.theta x - x) / x) ^ 2 / Real.log x := by
  have hx0 : 0 < x := (Real.exp_pos 2).trans_le hx
  have hL : (2 : ℝ) ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hx
  have hL0 : 0 < Real.log x := by linarith
  let Kclock := fun z : ℝ => Real.log (Real.log x) +
    (z - x) / (x * Real.log x) - Real.log (Real.log z)
  have hstab :=
    D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvatureStability.loglog_tangent_gap_stability_scaled
      (a := x) (x := Chebyshev.theta x) (y := x) hx htheta (by linarith)
  change |Kclock (Chebyshev.theta x) - Kclock x| ≤
    (16 / (x ^ 2 * Real.log x)) *
      (|x - x| * |Chebyshev.theta x - x| + |Chebyshev.theta x - x| ^ 2 / 2) at hstab
  have hKx : Kclock x = 0 := by dsimp [Kclock]; ring
  have hKN : Kclock (Chebyshev.theta x) = -N x := by dsimp [Kclock, N]; ring
  rw [hKN, hKx, sub_zero, abs_neg] at hstab
  have hstab' : |N x| ≤
      (16 / (x ^ 2 * Real.log x)) * ((Chebyshev.theta x - x) ^ 2 / 2) := by
    simpa only [sub_self, abs_zero, zero_mul, zero_add, sq_abs] using hstab
  calc
    _ ≤ (16 / (x ^ 2 * Real.log x)) * ((Chebyshev.theta x - x) ^ 2 / 2) := hstab'
    _ = _ := by field_simp [hx0.ne', hL0.ne']; ring

private lemma nonlinear_critical {alpha : ℝ} (ha : 0 < alpha) (hhalf : alpha ≤ 1 / 2)
    (hstrip : ∀ rho : ℂ, IsNontrivialZero rho → rho.re ≤ 1 - alpha) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
      |N x| ≤ (8 * K ^ 2) / (x ^ alpha * Real.log x) := by
  obtain ⟨K, R0, hK, hR0, htheta⟩ := strip_theta_rate ha hhalf hstrip
  have hu : Tendsto (fun x : ℝ => (Chebyshev.theta x - x) / x) atTop (𝓝 0) := by
    have hh := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2.sub
      (tendsto_const_nhds (x := (1 : ℝ)))
    simp only [sub_self] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
  apply Exists.intro K
  apply And.intro hK
  filter_upwards [eventually_ge_atTop R0,
    (show Tendsto (fun x : ℝ => |(Chebyshev.theta x - x) / x|) atTop (𝓝 0) by
      simpa only [abs_zero] using hu.abs).eventually_lt_const
        (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (Real.exp 2)] with x hxR hux hx
  have hx0 : 0 < x := (Real.exp_pos 2).trans_le hx
  have hL : (2 : ℝ) ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hx
  have hL0 : 0 < Real.log x := by linarith
  have hthetaHalf : x / 2 ≤ Chebyshev.theta x := by
    have hlow : -(1 / 2 : ℝ) < (Chebyshev.theta x - x) / x := (abs_lt.mp hux).1
    have hscaled := (lt_div_iff₀ hx0).mp hlow
    linarith
  have hpower : |(Chebyshev.theta x - x) / x| ≤ K * x ^ ((1 - alpha / 2) - 1) := by
    rw [abs_div, abs_of_pos hx0]
    calc
      _ ≤ (K * x ^ (1 - alpha / 2)) / x :=
        div_le_div_of_nonneg_right (htheta x hxR) hx0.le
      _ = K * x ^ ((1 - alpha / 2) - 1) := by
        rw [Real.rpow_sub_one hx0.ne']
        ring
  have hs := pow_le_pow_left₀ (abs_nonneg ((Chebyshev.theta x - x) / x)) hpower 2
  rw [sq_abs, mul_pow] at hs
  have hid : (x ^ ((1 - alpha / 2) - 1)) ^ 2 = x ^ (-alpha) := by
    rw [← Real.rpow_mul_natCast hx0.le]
    congr 1
    ring
  rw [hid] at hs
  calc
    _ ≤ 8 * ((Chebyshev.theta x - x) / x) ^ 2 / Real.log x :=
      nonlinear_quadratic hx hthetaHalf
    _ ≤ 8 * (K ^ 2 * x ^ (-alpha)) / Real.log x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by norm_num)) hL0.le
    _ = (8 * K ^ 2) / (x ^ alpha * Real.log x) := by
      rw [Real.rpow_neg hx0.le]
      field_simp [hL0.ne', (Real.rpow_pos_of_pos hx0 alpha).ne']

private lemma finite_critical {alpha : ℝ} (hhalf : alpha ≤ 1 / 2) :
    ∀ᶠ x : ℝ in atTop,
      |Mertens.E₃ x + Mertens.E₂p x| ≤ 4 / (x ^ alpha * Real.log x) := by
  have ha : 0 < 1 - alpha := by linarith
  have hsmall : ∀ᶠ x : ℝ in atTop, Real.log x / x ^ (1 - alpha) ≤ 1 :=
    ((isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ hx => hx.le)
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with x hs hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog : Real.log x ≤ x ^ (1 - alpha) := by
    simpa only [one_mul] using (div_le_iff₀ (Real.rpow_pos_of_pos hx0 _)).mp hs
  have hden : x ^ alpha * Real.log x ≤ x := by
    calc
      _ ≤ x ^ alpha * x ^ (1 - alpha) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx0.le _)
      _ = x := by
        rw [← Real.rpow_add hx0, show alpha + (1 - alpha) = (1 : ℝ) by ring,
          Real.rpow_one]
  exact (finite_cancellation hx).trans
    (div_le_div_of_nonneg_left (by norm_num)
      (mul_pos (Real.rpow_pos_of_pos hx0 _) hL0) hden)

/-- The complete actual zero strip controls the critical arithmetic envelope,
including alpha = 1/2, with no exponent slack in the conclusion. -/
theorem actual_B_critical_strip_envelope (alpha : Real) (hpositive : 0 < alpha)
    (hhalf : alpha ≤ 1/2)
    (hstrip : ∀ rho : Complex, D5.S3.Weil.ZeroSum.IsNontrivialZero rho → rho.re ≤ 1-alpha) :
    ∃ C T : Real, 0 ≤ C ∧ Real.exp 1 ≤ T ∧ ∀ x : Real, T ≤ x →
      abs (D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.B x) ≤
        C / (Real.rpow x alpha * Real.log x) := by
  obtain ⟨C0, hC0, hQ⟩ := Q_exp_bound hhalf hstrip
  obtain ⟨H, hH⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨K, hK, hN⟩ := nonlinear_critical hpositive hhalf hstrip
  let C : ℝ := 4 * C0 + 4 * |H| + 4 + 8 * K ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hevent : ∀ᶠ x : ℝ in atTop,
      |B x| ≤ C / (x ^ alpha * Real.log x) := by
    filter_upwards [hN, finite_critical hhalf, eventually_ge_atTop (2 : ℝ),
      eventually_ge_atTop (Real.exp 1)] with x hxN hxF hx2 hxe
    have hx0 : 0 < x := by linarith
    have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
    have hJ := Jpsi_bound hpositive hC0 hQ hx2 hxe
    have hS := S_bound hhalf hH hx2 hxe
    rw [(tails hx2).2.2]
    calc
      _ ≤ |Jpsi x - S x + (Mertens.E₃ x + Mertens.E₂p x)| + |N x| := abs_add_le _ _
      _ ≤ (|Jpsi x - S x| + |Mertens.E₃ x + Mertens.E₂p x|) + |N x| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ((|Jpsi x| + |S x|) + |Mertens.E₃ x + Mertens.E₂p x|) + |N x| :=
        add_le_add (add_le_add (abs_sub _ _) le_rfl) le_rfl
      _ ≤ (((4 * C0) / (x ^ alpha * Real.log x) +
          (4 * |H|) / (x ^ alpha * Real.log x)) +
          4 / (x ^ alpha * Real.log x)) + (8 * K ^ 2) / (x ^ alpha * Real.log x) :=
        add_le_add (add_le_add (add_le_add hJ hS) hxF) hxN
      _ = C / (x ^ alpha * Real.log x) := by dsimp [C]; ring
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp hevent
  apply Exists.intro C
  apply Exists.intro (max (Real.exp 1) T0)
  apply And.intro hC
  apply And.intro (le_max_left _ _)
  intro x hx
  exact hT0 x ((le_max_right _ _).trans hx)

end D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope

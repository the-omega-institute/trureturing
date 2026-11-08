/- GID: D5/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/RHSharpArithmeticEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Under RH actual arithmetic tails give the sharp B-envelope and lower liminf. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
import D5.S3.Weil.Mertens.Cryptids.Schoenfeld
import D5.S3.Arith.Robin.ThetaTailRobinWitness
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-! Actual arithmetic tail transport and the sharp lower endpoint under RH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U psiErrorKernel)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

namespace D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope

def D (x : ℝ) : ℝ := Real.sqrt x * Real.log x
def B (x : ℝ) : ℝ := Mertens.E₃ x +
  Real.log (Real.log (Chebyshev.theta x)) - Real.log (Real.log x)

private abbrev w := D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity
private def Jpsi (x : ℝ) : ℝ := ∫ t in Ioi x, (Chebyshev.psi t - t) * w t
private def S (x : ℝ) : ℝ := ∫ t in Ioi x, (Chebyshev.psi t - Chebyshev.theta t) * w t
private def N (x : ℝ) : ℝ := Real.log (Real.log (Chebyshev.theta x)) -
  Real.log (Real.log x) - (Chebyshev.theta x - x) / (x * Real.log x)

private lemma sqrt_Q {x : ℝ} (hx : 2 ≤ x) :
    Real.sqrt x * Q x = -G (Real.log x) := by
  have ht := D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable hx
  have hQ : Q x = -U x / x := by
    change Q x = _ at ht
    rw [ht]
    dsimp [U]
    field_simp [show x ≠ 0 by linarith]
    ring
  have hx0 : 0 < x := by linarith
  have he : Real.exp (-Real.log x / 2) = (Real.sqrt x)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0, ← Real.exp_neg]
    congr 1
    ring
  rw [hQ]
  simp only [G, Real.exp_log hx0, he]
  field_simp [(Real.sqrt_pos.mpr hx0).ne', hx0.ne']
  rw [Real.sq_sqrt hx0.le]
  ring

private lemma weighted_eq (t : ℝ) :
    psiErrorKernel t * D5.S3.Weil.Mertens.WeightedTailTransport.r t =
      (Chebyshev.psi t - t) * w t := by
  dsimp [psiErrorKernel, w, D5.S3.Weil.Mertens.WeightedTailTransport.r,
    D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity]
  ring

private lemma sqrt_exp (y : ℝ) : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  ring

private lemma Jpsi_signed_limit (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => D x * Jpsi x + G (Real.log x)) atTop (𝓝 0) := by
  let C := firstLiMass + 1
  have hG := (actual_G_control hRH).1 1 zero_lt_one
  have hC : 0 ≤ C := by
    obtain ⟨y, hy⟩ := hG.exists
    exact (abs_nonneg (G y)).trans hy.le
  obtain ⟨y0, hy0⟩ := eventually_atTop.mp hG
  let W := D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.W
  let R := D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.R
  let T : ℝ → ℝ := fun y => ∫ v in Ioi y, W v * Q (Real.exp v)
  have hbound : ∀ᶠ y : ℝ in atTop,
      |D (Real.exp y) * Jpsi (Real.exp y) + G y| ≤ C * (3 / y + 4 / y ^ 2) := by
    filter_upwards [eventually_ge_atTop (max (max y0 (Real.log 2)) 1)] with y hy
    have hy0' : y0 ≤ y := (le_max_left _ _).trans ((le_max_left _ _).trans hy)
    have hyl : Real.log 2 ≤ y := (le_max_right _ _).trans ((le_max_left _ _).trans hy)
    have hy1 : 1 ≤ y := (le_max_right _ _).trans hy
    have hypos : 0 < y := by linarith
    have hexp2 : 2 ≤ Real.exp y := by
      simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hyl
    have htr := D5.S3.Weil.Mertens.WeightedTailTransport.transport_exp hyl
      (D5.S3.Arith.Robin.CompleteMertensPeak.complete_mertens_ledger hexp2).1
    have hQ (v : ℝ) (hv : y ≤ v) : |Q (Real.exp v)| ≤ C * Real.exp (-v / 2) := by
      have hv2 : 2 ≤ Real.exp v := hexp2.trans (Real.exp_le_exp.mpr hv)
      have hs := sqrt_Q hv2
      rw [sqrt_exp, Real.log_exp] at hs
      have hg := (hy0 v (hy0'.trans hv)).le
      have he : Real.exp (v / 2) * Real.exp (-v / 2) = 1 := by
        rw [← Real.exp_add]; ring_nf; simp
      have hb := mul_le_mul_of_nonneg_left hg (Real.exp_nonneg (-v / 2))
      rw [← neg_neg (G v), ← hs, abs_neg, abs_mul,
        abs_of_pos (Real.exp_pos _)] at hb
      calc
        _ = Real.exp (v / 2) * Real.exp (-v / 2) * |Q (Real.exp v)| := by rw [he]; ring
        _ = Real.exp (-v / 2) * (Real.exp (v / 2) * |Q (Real.exp v)|) := by ring
        _ ≤ _ := hb
        _ = _ := by dsimp [C]; ring
    have hint : IntegrableOn (fun v : ℝ => W v * Q (Real.exp v)) (Ioi y) := htr.1
    have hmajor : IntegrableOn (fun v : ℝ => C * W y * Real.exp (-v / 2)) (Ioi y) := by
      have hh := (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) y).const_mul
        (C * W y)
      apply hh.congr
      filter_upwards [] with v
      congr 2
      ring
    have hT : |T y| ≤ 2 * C * W y * Real.exp (-y / 2) := by
      calc
        _ ≤ ∫ v in Ioi y, |W v * Q (Real.exp v)| := abs_integral_le_integral_abs
        _ ≤ ∫ v in Ioi y, C * W y * Real.exp (-v / 2) := by
          apply setIntegral_mono_on hint.abs hmajor measurableSet_Ioi
          intro v hv
          have hw := D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.W_nonneg
            (hypos.le.trans hv.le)
          have ha := D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.W_antitone
            hypos hv.le
          rw [abs_mul, abs_of_nonneg hw]
          exact (mul_le_mul_of_nonneg_left (hQ v hv.le) hw).trans (by
            dsimp [W] at *
            nlinarith [mul_nonneg hC (Real.exp_nonneg (-v / 2)),
              mul_le_mul_of_nonneg_right ha (mul_nonneg hC (Real.exp_nonneg (-v / 2)))])
        _ = 2 * C * W y * Real.exp (-y / 2) := by
          rw [integral_const_mul]
          have hi := integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) y
          have hi' : (∫ v in Ioi y, Real.exp (-v / 2)) =
              -Real.exp (-y / 2) / (-1 / 2) := by
            have hfun : (fun v : ℝ => Real.exp (-v / 2)) =
                (fun v => Real.exp ((-1 / 2) * v)) := by
              funext v
              congr 1
              ring
            rw [hfun, hi, show (-1 / 2 : ℝ) * y = -y / 2 by ring]
          rw [hi']
          ring
    have hwJ : D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail psiErrorKernel
        (Real.exp y) = Jpsi (Real.exp y) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact weighted_eq t
    have heq : D (Real.exp y) * Jpsi (Real.exp y) + G y =
        -G y / y - Real.exp (y / 2) * y * T y := by
      have ht := htr.2
      change R y * (Q (Real.exp y) -
        D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail psiErrorKernel (Real.exp y) /
          D5.S3.Weil.Mertens.WeightedTailTransport.r (Real.exp y)) = T y at ht
      rw [hwJ] at ht
      have hs := sqrt_Q hexp2
      rw [sqrt_exp, Real.log_exp] at hs
      have hr : D5.S3.Weil.Mertens.WeightedTailTransport.r (Real.exp y) = R y := by
        simp only [D5.S3.Weil.Mertens.WeightedTailTransport.r, R,
          D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.R, Real.log_exp, add_comm]
      have hR : R y ≠ 0 := by
        dsimp [R, D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.R]
        positivity
      rw [hr] at ht
      have htJ : Jpsi (Real.exp y) = R y * Q (Real.exp y) - T y := by
        have he : R y * Q (Real.exp y) - Jpsi (Real.exp y) = T y := by
          calc
            _ = R y * (Q (Real.exp y) - Jpsi (Real.exp y) / R y) := by
              field_simp [hR]
            _ = T y := ht
        linarith
      rw [htJ]
      dsimp [D, R, D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.R,
        D5.S3.Weil.Mertens.WeightedTailTransport.r]
      rw [sqrt_exp, Real.log_exp]
      field_simp [hypos.ne']
      linear_combination (y + 1) * hs
    rw [heq]
    calc
      _ ≤ |G y| / y + (Real.exp (y / 2) * y) * |T y| := by
        simpa [abs_div, abs_of_pos hypos, abs_mul, abs_of_pos (Real.exp_pos _)] using
          abs_sub (-G y / y) (Real.exp (y / 2) * y * T y)
      _ ≤ C / y + (Real.exp (y / 2) * y) *
          (2 * C * W y * Real.exp (-y / 2)) := by
        gcongr
        exact (hy0 y hy0').le
      _ = C * (3 / y + 4 / y ^ 2) := by
        have he : Real.exp (y / 2) * Real.exp (-y / 2) = 1 := by
          rw [← Real.exp_add]; ring_nf; simp
        dsimp [W, D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.W]
        field_simp [hypos.ne']
        calc
          _ = C * (y + 2 * (Real.exp (y / 2) * Real.exp (-y / 2)) * (y + 2)) := by ring
          _ = _ := by rw [he]; ring
  have hsmall : Tendsto (fun y : ℝ => C * (3 / y + 4 / y ^ 2)) atTop (𝓝 0) := by
    have hi : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv, inv_pow] using
      ((hi.const_mul 3).add ((hi.pow 2).const_mul 4)).const_mul C
  have he : Tendsto (fun y : ℝ => D (Real.exp y) * Jpsi (Real.exp y) + G y)
      atTop (𝓝 0) :=
    squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hbound) hsmall
  apply (he.comp Real.tendsto_log_atTop).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def, Real.exp_log hx]

private lemma psi_theta_log_root_rate_of_rh (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => Real.log x *
      ((Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x - 1)) atTop (𝓝 0) := by
  let C : ℝ := Real.log 4 + 4
  have hlogpow (n : ℕ) (s : ℝ) (hs : 0 < s) :
      Tendsto (fun x : ℝ => Real.log x ^ n / x ^ s) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (_root_.isLittleO_log_rpow_rpow_atTop (s := s) (n : ℝ) hs).tendsto_div_nhds_zero
  have hlimit : Tendsto (fun x : ℝ =>
      (7 / 32 : ℝ) * (Real.log x ^ 3 / x ^ (1 / 4 : ℝ)) +
        C * (Real.log x / x ^ (1 / 6 : ℝ)) +
        C * (Real.log x / x ^ (3 / 10 : ℝ))) atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, add_zero] using
      (((hlogpow 3 (1 / 4) (by norm_num)).const_mul (7 / 32 : ℝ)).add
        ((hlogpow 1 (1 / 6) (by norm_num)).const_mul C)).add
        ((hlogpow 1 (3 / 10) (by norm_num)).const_mul C)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hlimit
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_sqrt_atTop.eventually_ge_atTop (5000 : ℝ)] with x hx hx5000
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hw : 0 ≤ Real.log x / Real.sqrt x :=
    div_nonneg (Real.log_pos hx).le hs0.le
  have hu : Chebyshev.psi x - Chebyshev.theta x ≤
      Chebyshev.psi (Real.sqrt x) + Chebyshev.psi (x ^ (1 / 3 : ℝ)) +
        Chebyshev.psi (x ^ (1 / 5 : ℝ)) := by
    simpa only [Real.sqrt_eq_rpow, one_div] using
      Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hl : Chebyshev.psi (Real.sqrt x) ≤ Chebyshev.psi x - Chebyshev.theta x := by
    have hl' : Chebyshev.psi (Real.sqrt x) + Chebyshev.psi (x ^ (1 / 3 : ℝ)) +
        Chebyshev.psi (x ^ (1 / 7 : ℝ)) ≤ Chebyshev.psi x - Chebyshev.theta x := by
      simpa only [Real.sqrt_eq_rpow, one_div] using
        Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hx0.le
    linarith [Chebyshev.psi_nonneg (x ^ (1 / 3 : ℝ)),
      Chebyshev.psi_nonneg (x ^ (1 / 7 : ℝ))]
  have hgap : |Chebyshev.psi x - Chebyshev.theta x - Real.sqrt x| ≤
      |Chebyshev.psi (Real.sqrt x) - Real.sqrt x| +
        Chebyshev.psi (x ^ (1 / 3 : ℝ)) + Chebyshev.psi (x ^ (1 / 5 : ℝ)) := by
    apply abs_le.mpr
    constructor
    · have hb := neg_abs_le (Chebyshev.psi (Real.sqrt x) - Real.sqrt x)
      linarith [Chebyshev.psi_nonneg (x ^ (1 / 3 : ℝ)),
        Chebyshev.psi_nonneg (x ^ (1 / 5 : ℝ))]
    · have hb := le_abs_self (Chebyshev.psi (Real.sqrt x) - Real.sqrt x)
      linarith
  have hs :=
    ConjectureMachines.Semantics.Riemann.abs_psi_sub_self_le_seven_eighths_of_five_thousand_le
      hRH hx5000
  change |Chebyshev.psi (Real.sqrt x) - Real.sqrt x| ≤
    (7 / 8 : ℝ) * Real.sqrt (Real.sqrt x) * (Real.log (Real.sqrt x)) ^ 2 at hs
  have h3 : Chebyshev.psi (x ^ (1 / 3 : ℝ)) ≤ C * x ^ (1 / 3 : ℝ) :=
    Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx0.le _)
  have h5 : Chebyshev.psi (x ^ (1 / 5 : ℝ)) ≤ C * x ^ (1 / 5 : ℝ) :=
    Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx0.le _)
  have htotal : |Chebyshev.psi x - Chebyshev.theta x - Real.sqrt x| ≤
      (7 / 8 : ℝ) * Real.sqrt (Real.sqrt x) * (Real.log (Real.sqrt x)) ^ 2 +
        C * x ^ (1 / 3 : ℝ) + C * x ^ (1 / 5 : ℝ) := by
    linarith
  have hquarter : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    norm_num
  have hquot (r : ℝ) : x ^ r / Real.sqrt x = 1 / x ^ ((1 / 2 : ℝ) - r) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx0,
      show r - (1 / 2 : ℝ) = -((1 / 2 : ℝ) - r) by ring, Real.rpow_neg hx0.le]
    simp only [one_div]
  have hnormalize :
      (Real.log x / Real.sqrt x) *
          ((7 / 8 : ℝ) * Real.sqrt (Real.sqrt x) * (Real.log (Real.sqrt x)) ^ 2 +
            C * x ^ (1 / 3 : ℝ) + C * x ^ (1 / 5 : ℝ)) =
        (7 / 32 : ℝ) * (Real.log x ^ 3 / x ^ (1 / 4 : ℝ)) +
          C * (Real.log x / x ^ (1 / 6 : ℝ)) +
          C * (Real.log x / x ^ (3 / 10 : ℝ)) := by
    rw [Real.log_sqrt hx0.le, hquarter]
    calc
      _ = (7 / 32 : ℝ) * Real.log x ^ 3 * (x ^ (1 / 4 : ℝ) / Real.sqrt x) +
          C * Real.log x * (x ^ (1 / 3 : ℝ) / Real.sqrt x) +
          C * Real.log x * (x ^ (1 / 5 : ℝ) / Real.sqrt x) := by ring
      _ = _ := by
        rw [hquot (1 / 4), hquot (1 / 3), hquot (1 / 5)]
        norm_num; ring
  calc
    |Real.log x * ((Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x - 1)| =
        (Real.log x / Real.sqrt x) *
          |Chebyshev.psi x - Chebyshev.theta x - Real.sqrt x| := by
      have heq : Real.log x *
          ((Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x - 1) =
          (Real.log x / Real.sqrt x) *
            (Chebyshev.psi x - Chebyshev.theta x - Real.sqrt x) := by
        field_simp [hs0.ne']
      rw [heq, abs_mul, abs_of_nonneg hw]
    _ ≤ (Real.log x / Real.sqrt x) *
        ((7 / 8 : ℝ) * Real.sqrt (Real.sqrt x) * (Real.log (Real.sqrt x)) ^ 2 +
          C * x ^ (1 / 3 : ℝ) + C * x ^ (1 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left htotal hw
    _ = _ := hnormalize

private lemma psi_theta_root_limit_of_rh (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x)
      atTop (𝓝 1) := by
  have hrate := psi_theta_log_root_rate_of_rh hRH
  have hinv : Tendsto (fun x : ℝ => 1 / Real.log x) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hzero : Tendsto (fun x : ℝ =>
      (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x - 1) atTop (𝓝 0) := by
    have hprod : Tendsto (fun x : ℝ =>
        (Real.log x * ((Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x - 1)) *
          (1 / Real.log x)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hrate.mul hinv
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    calc
      _ = ((1 / Real.log x) * Real.log x) *
          ((Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x - 1) := by ring
      _ = _ := by rw [one_div, inv_mul_cancel₀ hl, one_mul]
  simpa only [zero_add, sub_add_cancel] using hzero.add_const 1

private lemma theta_error (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => (Chebyshev.theta x - x) / x ^ (3 / 4 : ℝ)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hlog : Tendsto (fun x : ℝ => Real.log x ^ 2 / x ^ (1 / 4 : ℝ))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (_root_.isLittleO_log_rpow_rpow_atTop (s := (1 / 4 : ℝ)) ((2 : ℕ) : ℝ)
        (by norm_num)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => 1 / x ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (y := (1 / 4 : ℝ)) (by norm_num))
  have hbound : Tendsto (fun x : ℝ =>
      (7 / 8 : ℝ) * (Real.log x ^ 2 / x ^ (1 / 4 : ℝ)) + C / x ^ (1 / 4 : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, mul_one_div] using
      (hlog.const_mul (7 / 8 : ℝ)).add (hinv.const_mul C)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hbound
  filter_upwards [eventually_ge_atTop (5000 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hp :=
    ConjectureMachines.Semantics.Riemann.abs_psi_sub_self_le_seven_eighths_of_five_thousand_le
      hRH hx
  change |Chebyshev.psi x - x| ≤
    (7 / 8 : ℝ) * Real.sqrt x * Real.log x ^ 2 at hp
  have hgap0 : 0 ≤ Chebyshev.psi x - Chebyshev.theta x :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  have herr : |Chebyshev.theta x - x| ≤
      |Chebyshev.psi x - x| + (Chebyshev.psi x - Chebyshev.theta x) := by
    apply abs_le.mpr
    constructor
    · have hb := neg_abs_le (Chebyshev.psi x - x)
      linarith
    · have hb := le_abs_self (Chebyshev.psi x - x)
      linarith
  have herr' : |Chebyshev.theta x - x| ≤
      (7 / 8 : ℝ) * Real.sqrt x * Real.log x ^ 2 + C * Real.sqrt x := by
    linarith [hC x]
  have hquot : Real.sqrt x / x ^ (3 / 4 : ℝ) = 1 / x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx0,
      show (1 / 2 : ℝ) - 3 / 4 = -(1 / 4 : ℝ) by norm_num,
      Real.rpow_neg hx0.le]
    simp only [one_div]
  calc
    |(Chebyshev.theta x - x) / x ^ (3 / 4 : ℝ)| =
        |Chebyshev.theta x - x| / x ^ (3 / 4 : ℝ) := by
      rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    _ ≤ ((7 / 8 : ℝ) * Real.sqrt x * Real.log x ^ 2 + C * Real.sqrt x) /
        x ^ (3 / 4 : ℝ) :=
      div_le_div_of_nonneg_right herr' (Real.rpow_nonneg hx0.le _)
    _ = (7 / 8 : ℝ) * (Real.log x ^ 2 / x ^ (1 / 4 : ℝ)) +
        C / x ^ (1 / 4 : ℝ) := by
      calc
        _ = (7 / 8 : ℝ) * Real.log x ^ 2 * (Real.sqrt x / x ^ (3 / 4 : ℝ)) +
            C * (Real.sqrt x / x ^ (3 / 4 : ℝ)) := by ring
        _ = _ := by rw [hquot]; ring

private lemma theta_late (hRH : RiemannHypothesis) :
    ∀ᶠ x : ℝ in atTop, 1 < Chebyshev.theta x := by
  have htheta_rate := theta_error hRH
  have hinv : Tendsto (fun x : ℝ => 1 / x ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (y := (1 / 4 : ℝ)) (by norm_num))
  have hrelative : Tendsto (fun x : ℝ => (Chebyshev.theta x - x) / x)
      atTop (𝓝 0) := by
    have hprod : Tendsto (fun x : ℝ =>
        ((Chebyshev.theta x - x) / x ^ (3 / 4 : ℝ)) * (1 / x ^ (1 / 4 : ℝ)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using htheta_rate.mul hinv
    refine hprod.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hpowers : x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x := by
      rw [← Real.rpow_add hx]
      norm_num
    calc
      _ = (Chebyshev.theta x - x) / (x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by
        rw [div_mul_div_comm, mul_one]
      _ = _ := by rw [hpowers]
  have hratio : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
    have hplus : Tendsto (fun x : ℝ => (Chebyshev.theta x - x) / x + 1)
        atTop (𝓝 1) := by
      simpa only [zero_add] using hrelative.add_const 1
    refine hplus.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']; ring
  filter_upwards [eventually_gt_atTop (2 : ℝ),
    hratio.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))] with x hx ht
  have hx0 : 0 < x := by linarith
  have hhalf : (1 / 2 : ℝ) * x < Chebyshev.theta x := (lt_div_iff₀ hx0).mp ht
  linarith

private lemma N_limit (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => D x * N x) atTop (𝓝 0) := by
  let delta : ℝ → ℝ := fun x => Chebyshev.theta x - x
  let u : ℝ → ℝ := fun x => delta x / x
  have hu : Tendsto u atTop (𝓝 0) := by
    have hh := (theta_error hRH).mul
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4))
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp [u, delta]
    rw [show (-(1 / 4) : ℝ) = (3 / 4 : ℝ) - 1 by norm_num, Real.rpow_sub hx,
      Real.rpow_one]
    field_simp [(Real.rpow_pos_of_pos hx (3 / 4 : ℝ)).ne']
  have hbound : ∀ᶠ x : ℝ in atTop,
      |D x * N x| ≤ 10 * ((Chebyshev.theta x - x) / x ^ (3 / 4 : ℝ)) ^ 2 := by
    filter_upwards [
      (show Tendsto (fun x => |u x|) atTop (𝓝 0) by simpa using hu.abs).eventually_lt_const
        (by norm_num : (0 : ℝ) < 1 / 4),
      Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_gt_atTop (1 : ℝ)] with x hux hL hx
    let L := Real.log x
    let v := Real.log (1 + u x) / L
    have hx0 : 0 < x := by linarith
    have hL0 : 0 < L := by dsimp [L]; exact Real.log_pos hx
    have hu1 : 0 < 1 + u x := by linarith [(abs_lt.mp hux).1]
    have hlogu : |Real.log (1 + u x) - u x| ≤ 2 * (u x) ^ 2 := by
      have ht := Real.abs_log_sub_add_sum_range_le (x := -u x)
        (by rw [abs_neg]; linarith) 1
      simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one,
        sub_neg_eq_add, abs_neg, show 1 + 1 = (2 : ℕ) by decide] at ht
      have hd : 0 < 1 - |u x| := by linarith
      have hs : |u x| ^ 2 = (u x) ^ 2 := sq_abs _
      rw [hs] at ht
      have ht' : |Real.log (1 + u x) - u x| ≤ (u x) ^ 2 / (1 - |u x|) := by
        simpa only [sub_eq_add_neg, add_comm] using ht
      exact ht'.trans ((div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg (u x)]))
    have hlogabs : |Real.log (1 + u x)| ≤ 2 * |u x| := by
      have ht := abs_add_le (Real.log (1 + u x) - u x) (u x)
      rw [sub_add_cancel] at ht
      nlinarith [sq_abs (u x), abs_nonneg (u x)]
    have hv : |v| ≤ 1 / 2 := by
      dsimp [v]
      rw [abs_div, abs_of_pos hL0]
      apply (div_le_iff₀ hL0).mpr
      dsimp [L] at *
      linarith
    have hlogv : |Real.log (1 + v) - v| ≤ 2 * v ^ 2 := by
      have ht := Real.abs_log_sub_add_sum_range_le (x := -v)
        (by rw [abs_neg]; linarith) 1
      simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one,
        sub_neg_eq_add, abs_neg, show 1 + 1 = (2 : ℕ) by decide] at ht
      have hd : 0 < 1 - |v| := by linarith
      rw [sq_abs] at ht
      have ht' : |Real.log (1 + v) - v| ≤ v ^ 2 / (1 - |v|) := by
        simpa only [sub_eq_add_neg, add_comm] using ht
      exact ht'.trans ((div_le_iff₀ hd).mpr (by nlinarith [sq_nonneg v]))
    have htheta : Chebyshev.theta x = x * (1 + u x) := by
      dsimp [u, delta]
      field_simp [hx0.ne']
      ring
    have hlogtheta : Real.log (Chebyshev.theta x) = L * (1 + v) := by
      rw [htheta, Real.log_mul hx0.ne' hu1.ne']
      dsimp [v, L]
      field_simp [hL0.ne']
    have hid : N x = (Real.log (1 + v) - v) +
        (Real.log (1 + u x) - u x) / L := by
      dsimp [N]
      rw [hlogtheta, Real.log_mul hL0.ne' (by linarith [(abs_le.mp hv).1] : 1 + v ≠ 0)]
      dsimp [v, u, delta, L]
      field_simp [hx0.ne', hL0.ne']
      ring
    have hv2 : v ^ 2 ≤ 4 * (u x) ^ 2 / L ^ 2 := by
      have ht : |v| ≤ 2 * |u x| / L := by
        dsimp [v]
        rw [abs_div, abs_of_pos hL0]
        exact div_le_div_of_nonneg_right hlogabs hL0.le
      have hs := pow_le_pow_left₀ (abs_nonneg v) ht 2
      norm_num only [div_pow, mul_pow, sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] at hs
      exact hs
    have hN : |N x| ≤ 10 * (u x) ^ 2 / L := by
      rw [hid]
      have hh := abs_add_le (Real.log (1 + v) - v) ((Real.log (1 + u x) - u x) / L)
      rw [abs_div, abs_of_pos hL0] at hh
      have hh' := div_le_div_of_nonneg_right hlogu hL0.le
      have hL1 : 1 ≤ L := hL
      have hvb : v ^ 2 ≤ 4 * (u x) ^ 2 / L := by
        exact hv2.trans (div_le_div_of_nonneg_left (by positivity) hL0 (by nlinarith))
      calc
        _ ≤ |Real.log (1 + v) - v| + |Real.log (1 + u x) - u x| / L := hh
        _ ≤ 2 * v ^ 2 + 2 * (u x) ^ 2 / L := add_le_add hlogv hh'
        _ ≤ 2 * (4 * (u x) ^ 2 / L) + 2 * (u x) ^ 2 / L := by gcongr
        _ = _ := by ring
    have hD : 0 ≤ D x := by dsimp [D]; positivity
    rw [abs_mul, abs_of_nonneg hD]
    calc
      _ ≤ D x * (10 * (u x) ^ 2 / L) := mul_le_mul_of_nonneg_left hN hD
      _ = 10 * ((Chebyshev.theta x - x) / x ^ (3 / 4 : ℝ)) ^ 2 := by
        have hp : (x ^ (3 / 4 : ℝ)) ^ 2 = x * Real.sqrt x := by
          calc
            _ = x ^ ((3 / 4 : ℝ) * 2) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
              norm_num
            _ = x ^ ((1 : ℝ) + 1 / 2) := by norm_num
            _ = x * Real.sqrt x := by
              rw [Real.rpow_add hx0, Real.rpow_one, Real.sqrt_eq_rpow]
        dsimp [D, u, delta, L]
        field_simp [hx0.ne', hL0.ne', (Real.rpow_pos_of_pos hx0 (3 / 4 : ℝ)).ne']
        rw [hp]
        ring_nf
        rw [Real.sq_sqrt hx0.le]
        ring
  exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using hbound)
    (by simpa using ((theta_error hRH).pow 2).const_mul 10)

private def a (t : ℝ) : ℝ := Real.sqrt t * w t
private def H (t : ℝ) : ℝ := 2 / (Real.sqrt t * Real.log t)
private def q (t : ℝ) : ℝ := (Real.log t + 2) /
  (t * Real.sqrt t * (Real.log t) ^ 2)
private def A (x : ℝ) : ℝ := ∫ t in Ioi x, a t

private lemma neg_H_deriv {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun z => -H z) (q t) t := by
  have ht0 : 0 < t := by linarith
  have hs := Real.sqrt_pos.mpr ht0
  have hl := Real.log_pos ht
  have hd := ((hasDerivAt_const t (2 : ℝ)).div
    ((Real.hasDerivAt_sqrt ht0.ne').mul (Real.hasDerivAt_log ht0.ne'))
      (mul_ne_zero hs.ne' hl.ne')).neg
  apply hd.congr_deriv
  dsimp [q]
  field_simp [ht0.ne', hs.ne', hl.ne']
  rw [Real.sq_sqrt ht0.le]
  ring

private lemma H_zero : Tendsto H atTop (𝓝 0) := by
  have hh : Tendsto (fun t : ℝ => Real.sqrt t * Real.log t) atTop atTop :=
    Real.tendsto_sqrt_atTop.atTop_mul_atTop₀ Real.tendsto_log_atTop
  exact tendsto_const_nhds.div_atTop hh

private lemma q_bounds {x t : ℝ} (hx : 1 < x) (hxt : x ≤ t) :
    0 ≤ a t ∧ a t ≤ q t ∧ q t ≤ (1 + 1 / Real.log x) * a t := by
  have ht : 1 < t := hx.trans_le hxt
  have ht0 : 0 < t := by linarith
  have hs := Real.sqrt_pos.mpr ht0
  have hl := Real.log_pos ht
  have hlx := Real.log_pos hx
  have hlog := Real.log_le_log (by linarith : 0 < x) hxt
  dsimp [a, q, w, D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity]
  refine ⟨by positivity, ?_, ?_⟩
  · field_simp [ht0.ne', hs.ne', hl.ne']
    nlinarith [Real.sq_sqrt ht0.le]
  · field_simp [ht0.ne', hs.ne', hl.ne', hlx.ne']
    rw [Real.sq_sqrt ht0.le]
    nlinarith only [ht0.le, mul_nonneg ht0.le (sub_nonneg.mpr hlog)]

private lemma A_data {x : ℝ} (hx : 1 < x) :
    IntegrableOn a (Ioi x) ∧ H x / (1 + 1 / Real.log x) ≤ A x ∧ A x ≤ H x := by
  have hqpos : ∀ t ∈ Ioi x, 0 ≤ q t := by
    intro t ht
    exact (q_bounds hx ht.le).1.trans (q_bounds hx ht.le).2.1
  have hq : IntegrableOn q (Ioi x) := integrableOn_Ioi_deriv_of_nonneg'
    (fun t ht => neg_H_deriv (hx.trans_le ht)) hqpos (by simpa using H_zero.neg)
  have hqi : (∫ t in Ioi x, q t) = H x := by
    have hh := integral_Ioi_of_hasDerivAt_of_nonneg'
      (a := x) (g := fun t => -H t) (g' := q) (l := (0 : ℝ))
      (fun t ht => neg_H_deriv (hx.trans_le ht)) hqpos (by simpa using H_zero.neg)
    calc
      _ = (0 : ℝ) - (-H x) := hh
      _ = H x := by ring
  have ha : IntegrableOn a (Ioi x) := by
    have hcont : ContinuousOn a (Ioi x) := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt (lt_trans (by linarith : 0 < x) ht)
      have hl0 : Real.log t ≠ 0 := (Real.log_pos (hx.trans ht)).ne'
      exact (Real.continuous_sqrt.continuousAt.mul
        (((Real.continuousAt_log ht0).add continuousAt_const).div
          ((continuousAt_id.pow 2).mul ((Real.continuousAt_log ht0).pow 2))
          (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hl0)))).continuousWithinAt
    apply hq.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (q_bounds hx ht.le).1]
    exact (q_bounds hx ht.le).2.1
  have hupper : A x ≤ H x := by
    rw [← hqi]
    exact setIntegral_mono_on ha hq measurableSet_Ioi (fun t ht => (q_bounds hx ht.le).2.1)
  have hlower : H x ≤ (1 + 1 / Real.log x) * A x := by
    rw [← hqi, A, ← integral_const_mul]
    exact setIntegral_mono_on hq (ha.const_mul _) measurableSet_Ioi
      (fun t ht => (q_bounds hx ht.le).2.2)
  refine ⟨ha, ?_, hupper⟩
  apply (div_le_iff₀ (by have := Real.log_pos hx; positivity)).mpr
  simpa only [mul_comm] using hlower

private lemma A_limit : Tendsto (fun x : ℝ => D x * A x) atTop (𝓝 2) := by
  have hi : Tendsto (fun x : ℝ => 1 / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hlow : Tendsto (fun x : ℝ => 2 / (1 + 1 / Real.log x)) atTop (𝓝 2) := by
    have hden : Tendsto (fun x : ℝ => 1 + 1 / Real.log x) atTop (𝓝 1) := by
      simpa only [add_zero] using hi.const_add 1
    have hmul := hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [div_eq_mul_inv] using hmul.const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have h := mul_le_mul_of_nonneg_left (A_data hx).2.1
      (by dsimp [D]; have := Real.log_pos hx; positivity : 0 ≤ D x)
    have hDH : D x * H x = 2 := by
      dsimp [D, H]
      field_simp [(Real.sqrt_pos.mpr (by linarith : 0 < x)).ne', (Real.log_pos hx).ne']
    simpa only [← mul_div_assoc, hDH] using h
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have h := mul_le_mul_of_nonneg_left (A_data hx).2.2
      (by dsimp [D]; have := Real.log_pos hx; positivity : 0 ≤ D x)
    have hDH : D x * H x = 2 := by
      dsimp [D, H]
      field_simp [(Real.sqrt_pos.mpr (by linarith : 0 < x)).ne', (Real.log_pos hx).ne']
    rwa [hDH] at h


private lemma tails {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t => (Chebyshev.psi t - t) * w t) (Ioi x) ∧
    IntegrableOn (fun t => (Chebyshev.psi t - Chebyshev.theta t) * w t) (Ioi x) ∧
    B x = Jpsi x - S x + (Mertens.E₃ x + Mertens.E₂p x) + N x := by
  have hp := (D5.S3.Arith.Robin.CompleteMertensPeak.complete_mertens_ledger hx).2.1
  have hp' : IntegrableOn (fun t => (Chebyshev.psi t - t) * w t) (Ioi x) := by
    simpa only [weighted_eq] using hp
  have ht := D5.S3.Arith.Robin.ThetaTailRobinWitness.theta_tail_mertens_robin x hx
  have hs : IntegrableOn (fun t => (Chebyshev.psi t - Chebyshev.theta t) * w t) (Ioi x) := by
    convert hp'.sub ht.1 using 1
    ext t
    dsimp [w]
    ring
  refine ⟨hp', hs, ?_⟩
  have hsub : Jpsi x - S x = ∫ t in Ioi x, (Chebyshev.theta t - t) * w t := by
    rw [Jpsi, S, ← integral_sub hp' hs]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    ring
  rw [hsub]
  dsimp [B, N]
  linarith [ht.2.1]

private lemma S_limit (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => D x * S x) atTop (𝓝 2) := by
  rw [Metric.tendsto_nhds]
  intro epsilon he
  have hroot := psi_theta_root_limit_of_rh hRH
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hroot)
    (epsilon / 6) (by positivity))
  filter_upwards [eventually_ge_atTop (max T 2),
    (Metric.tendsto_nhds.mp A_limit) (epsilon / 2) (by positivity),
    A_limit.eventually (gt_mem_nhds (by norm_num : (2 : ℝ) < 3))] with x hx hAx hA3
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 < x := by linarith
  have hi := (tails hx2).2.1
  have ha := (A_data hx1).1
  have hpoint (t : ℝ) (ht : t ∈ Ioi x) :
      |((Chebyshev.psi t - Chebyshev.theta t) * w t) - a t| ≤ (epsilon / 6) * a t := by
    have ht0 : 0 < t := lt_trans (by linarith : 0 < x) ht
    have hs := Real.sqrt_pos.mpr ht0
    have hh := hT t (((le_max_left _ _).trans hx).trans ht.le)
    simp only [Real.dist_eq] at hh
    have hw : 0 ≤ w t := by
      dsimp [w, D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity]
      have := Real.log_pos (hx1.trans ht)
      positivity
    have heq : ((Chebyshev.psi t - Chebyshev.theta t) * w t) - a t =
        ((Chebyshev.psi t - Chebyshev.theta t) / Real.sqrt t - 1) * a t := by
      dsimp [a]
      field_simp [hs.ne']
    rw [heq, abs_mul, abs_of_nonneg (q_bounds hx1 ht.le).1]
    exact mul_le_mul_of_nonneg_right hh.le (q_bounds hx1 ht.le).1
  have hdiff : |S x - A x| ≤ (epsilon / 6) * A x := by
    rw [S, A, ← integral_sub hi ha, ← integral_const_mul]
    exact (abs_integral_le_integral_abs).trans
      (setIntegral_mono_on (hi.sub ha).abs (ha.const_mul _) measurableSet_Ioi hpoint)
  have hD : 0 ≤ D x := by dsimp [D]; have := Real.log_pos hx1; positivity
  have hscaled : |D x * (S x - A x)| ≤ epsilon / 2 := by
    rw [abs_mul, abs_of_nonneg hD]
    have hh := mul_le_mul_of_nonneg_left hdiff hD
    nlinarith [hA3]
  simp only [Real.dist_eq] at hAx ⊢
  calc
    _ = |D x * (S x - A x) + (D x * A x - 2)| := by congr 1; ring
    _ ≤ |D x * (S x - A x)| + |D x * A x - 2| := abs_add_le _ _
    _ < epsilon := by linarith

private lemma finite_cancellation {x : ℝ} (hx : 2 ≤ x) :
    |Mertens.E₃ x + Mertens.E₂p x| ≤ 4 / x := by
  have hid : Mertens.E₃ x + Mertens.E₂p x =
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Mertens.M_eq_summand n) - (Mertens.M - Mertens.γ) := by
    have hs : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with n.Prime, Real.log (1 - (1 : ℝ) / n)) +
        (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with n.Prime, (1 : ℝ) / n) =
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Mertens.M_eq_summand n := by
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Mertens.M_eq_summand]
      split_ifs <;> ring
    unfold Mertens.E₃ Mertens.E₂p
    rw [Mertens.γ.eq_eulerMascheroni]
    linarith [hs]
  rw [hid]
  exact Mertens.sum_M_eq_summand_le' hx

private lemma finite_limit :
    Tendsto (fun x : ℝ => D x * (Mertens.E₃ x + Mertens.E₂p x)) atTop (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ => 4 * Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, mul_div_assoc, mul_zero] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.const_mul 4
  apply squeeze_zero_norm' ?_ hl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hD : 0 ≤ D x := by dsimp [D]; have := Real.log_pos (by linarith : 1 < x); positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hD]
  calc
    _ ≤ D x * (4 / x) := mul_le_mul_of_nonneg_left (finite_cancellation hx) hD
    _ = 4 * Real.log x / Real.sqrt x := by
      dsimp [D]
      field_simp [hx0.ne', (Real.sqrt_pos.mpr hx0).ne']
      rw [Real.sq_sqrt hx0.le]
      ring

private lemma signed_B_limit (hRH : RiemannHypothesis) :
    Tendsto (fun x : ℝ => D x * B x + 2 + G (Real.log x)) atTop (𝓝 0) := by
  have h := (((Jpsi_signed_limit hRH).sub ((S_limit hRH).sub_const 2)).add finite_limit).add
    (N_limit hRH)
  simp only [zero_add, sub_self] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [(tails hx).2.2]
  ring

/-- The sharp lower endpoint on all sufficiently late real endpoints, including its exact liminf. -/
theorem actual_B_lower_endpoint (hRH : RiemannHypothesis) :
    (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ x : ℝ in atTop,
      1 < Chebyshev.theta x ∧ |D x * B x + 2| < firstLiMass + epsilon) ∧
    (∀ epsilon : ℝ, 0 < epsilon → ∀ Y : ℝ,
      ∃ x : ℝ, max 2 Y ≤ x ∧ 1 < Chebyshev.theta x ∧
        |D x * B x + 2 + firstLiMass| < epsilon) ∧
    Filter.liminf (fun x : ℝ => D x * B x) atTop = -2 - firstLiMass := by
  have henv : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ x : ℝ in atTop,
      1 < Chebyshev.theta x ∧ |D x * B x + 2| < firstLiMass + epsilon := by
    intro epsilon he
    filter_upwards [theta_late hRH,
      Real.tendsto_log_atTop.eventually ((actual_G_control hRH).1 (epsilon / 2) (by positivity)),
      (Metric.tendsto_nhds.mp (signed_B_limit hRH)) (epsilon / 2) (by positivity)] with x ht hg hb
    refine ⟨ht, ?_⟩
    simp only [Real.dist_eq, sub_zero] at hb
    have hh := abs_sub (D x * B x + 2 + G (Real.log x)) (G (Real.log x))
    rw [add_sub_cancel_right] at hh
    linarith
  have hatt : ∀ epsilon : ℝ, 0 < epsilon → ∀ Y : ℝ,
      ∃ x : ℝ, max 2 Y ≤ x ∧ 1 < Chebyshev.theta x ∧
        |D x * B x + 2 + firstLiMass| < epsilon := by
    intro epsilon he Y
    have hevent := (theta_late hRH).and
      ((Metric.tendsto_nhds.mp (signed_B_limit hRH)) (epsilon / 3) (by positivity))
    obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
    let Z := Real.log (max (max T 2) (max Y 1))
    obtain ⟨n, hn, hg⟩ := (actual_G_control hRH).2 (2 * epsilon / 3) (by positivity) Z
    let x := Real.exp (n : ℝ)
    have hx : max (max T 2) (max Y 1) ≤ x := by
      have hh := Real.exp_le_exp.mpr hn
      simpa only [Z, Real.exp_log (by positivity : 0 < max (max T 2) (max Y 1))] using hh
    have hxT : T ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
    obtain ⟨ht, hb⟩ := hT x hxT
    refine ⟨x, max_le ((le_max_right _ _).trans ((le_max_left _ _).trans hx))
      ((le_max_left _ _).trans ((le_max_right _ _).trans hx)), ht, ?_⟩
    simp only [Real.dist_eq, sub_zero, x, Real.log_exp] at hb
    have hh := abs_sub (D x * B x + 2 + G (n : ℝ)) (G (n : ℝ) - firstLiMass)
    have hi : D x * B x + 2 + G (n : ℝ) - (G (n : ℝ) - firstLiMass) =
        D x * B x + 2 + firstLiMass := by ring
    rw [hi] at hh
    linarith
  have hlower : atTop.IsBoundedUnder (· ≥ ·) (fun x : ℝ => D x * B x) := by
    apply isBoundedUnder_of_eventually_ge (a := -2 - firstLiMass - 1)
    filter_upwards [henv 1 zero_lt_one] with x hx
    linarith [(abs_lt.mp hx.2).1]
  have hupper : atTop.IsBoundedUnder (· ≤ ·) (fun x : ℝ => D x * B x) := by
    apply isBoundedUnder_of_eventually_le (a := -2 + firstLiMass + 1)
    filter_upwards [henv 1 zero_lt_one] with x hx
    linarith [(abs_lt.mp hx.2).2]
  have hlim : Filter.liminf (fun x : ℝ => D x * B x) atTop = -2 - firstLiMass := by
    apply le_antisymm
    · apply (liminf_le_iff hupper.isCoboundedUnder_ge hlower).mpr
      intro y hy
      rw [frequently_atTop]
      intro Y
      obtain ⟨x, hx, ht, hb⟩ := hatt ((y - (-2 - firstLiMass)) / 2) (by linarith) Y
      exact ⟨x, (le_max_right _ _).trans hx, by linarith [(abs_lt.mp hb).2]⟩
    · apply (le_liminf_iff hupper.isCoboundedUnder_ge hlower).mpr
      intro y hy
      filter_upwards [henv (((-2 - firstLiMass) - y) / 2) (by linarith)] with x hx
      linarith [(abs_lt.mp hx.2).1]
  exact ⟨henv, hatt, hlim⟩

end D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope

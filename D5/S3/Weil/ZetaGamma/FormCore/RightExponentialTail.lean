/- GID: D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTail
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:half-line-analytic-operator)
   anchors: []
   utility: none
   digest: Exact half-line exponential-tail balances with actual endpoint and derivative-of-weight charges. -/

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact half-line energy balances for the literal right exponential tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

open MeasureTheory Set Filter
open scoped Topology

private def weightedInput (k : ℝ) (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-k * t) : ℂ) * u t

/-- The actual right exponential tail. On a continuous compactly supported
input it is defined at every real point, for every real `k`. -/
def rightExponentialTail (k : ℝ) (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s : ℝ in Ioi 0, (Real.exp (-k * s) : ℂ) * u (t + s)

private theorem integral_translate_halfline (f : ℝ → ℂ) (t : ℝ) :
    (∫ s : ℝ in Ioi 0, f (t + s)) = ∫ s : ℝ in Ioi t, f s := by
  calc
    (∫ s : ℝ in Ioi 0, f (t + s)) =
        ∫ s : ℝ, (Ioi 0).indicator (fun x : ℝ => f (t + x)) s :=
      (integral_indicator measurableSet_Ioi).symm
    _ = ∫ s : ℝ, (Ioi t).indicator f (t + s) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        by_cases hs : 0 < s
        · have ht : t < t + s := by linarith
          simp only [Set.indicator_apply, Set.mem_Ioi, if_pos hs, if_pos ht]
        · have ht : ¬ t < t + s := by linarith
          simp only [Set.indicator_apply, Set.mem_Ioi, if_neg hs, if_neg ht]
    _ = ∫ s : ℝ, (Ioi t).indicator f s := integral_add_left_eq_self _ t
    _ = ∫ s : ℝ in Ioi t, f s := integral_indicator measurableSet_Ioi

private theorem tail_eq_weighted (k : ℝ) (u : ℝ → ℂ) (t : ℝ) :
    rightExponentialTail k u t =
      (Real.exp (k * t) : ℂ) * ∫ s : ℝ in Ioi t, weightedInput k u s := by
  calc
    rightExponentialTail k u t =
        ∫ s : ℝ in Ioi 0, (Real.exp (k * t) : ℂ) * weightedInput k u (t + s) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        have he : (Real.exp (-k * s) : ℂ) =
            (Real.exp (k * t) : ℂ) * (Real.exp (-k * (t + s)) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Real.exp_add]
          congr 2
          ring
        change (Real.exp (-k * s) : ℂ) * u (t + s) = _
        rw [he]
        simp only [weightedInput, mul_assoc]
    _ = (Real.exp (k * t) : ℂ) * ∫ s : ℝ in Ioi 0, weightedInput k u (t + s) :=
      integral_const_mul _ _
    _ = _ := congrArg (fun z : ℂ => (Real.exp (k * t) : ℂ) * z)
      (integral_translate_halfline (weightedInput k u) t)

private theorem weightedInput_continuous {u : ℝ → ℂ} (hu : Continuous u) (k : ℝ) :
    Continuous (weightedInput k u) := by
  unfold weightedInput
  fun_prop

private theorem weightedInput_integrable {u : ℝ → ℂ}
    (hu : Continuous u) (hs : HasCompactSupport u) (k : ℝ) :
    Integrable (weightedInput k u) volume := by
  apply (weightedInput_continuous hu k).integrable_of_hasCompactSupport
  exact hs.mul_left

private theorem exists_upper_zero {u : ℝ → ℂ} (hs : HasCompactSupport u) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R ≤ t → u t = 0 := by
  have hc : IsCompact (tsupport u) := hs
  obtain ⟨M, hM⟩ := hc.bddAbove
  refine ⟨max M 0 + 1, by positivity, ?_⟩
  intro t ht
  by_contra hn
  have htSupport : t ∈ tsupport u :=
    subset_closure (show t ∈ Function.support u from hn)
  have hbound : t ≤ M := hM htSupport
  have hmax : M ≤ max M 0 := le_max_left _ _
  linarith

private theorem tail_eq_interval {u : ℝ → ℂ}
    (hu : Continuous u) (hs : HasCompactSupport u) (k R t : ℝ)
    (hz : ∀ s : ℝ, R ≤ s → u s = 0) :
    rightExponentialTail k u t =
      (Real.exp (k * t) : ℂ) * ∫ s : ℝ in t..R, weightedInput k u s := by
  have hi := weightedInput_integrable hu hs k
  have hzero : (∫ s : ℝ in Ioi R, weightedInput k u s) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hS
    simp only [weightedInput, hz s hS.le, mul_zero, Pi.zero_apply]
  have he := intervalIntegral.integral_Ioi_sub_Ioi'
    (a := t) (b := R) hi.integrableOn hi.integrableOn
  rw [hzero, sub_zero] at he
  rw [tail_eq_weighted]
  exact congrArg (fun z : ℂ => (Real.exp (k * t) : ℂ) * z) he

private theorem tail_zero_above {u : ℝ → ℂ}
    (k R t : ℝ) (hz : ∀ s : ℝ, R ≤ s → u s = 0) (ht : R ≤ t) :
    rightExponentialTail k u t = 0 := by
  have hzero : (∫ s : ℝ in Ioi t, weightedInput k u s) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hS
    simp only [weightedInput, hz s (ht.trans hS.le), mul_zero, Pi.zero_apply]
  rw [tail_eq_weighted, hzero, mul_zero]

private theorem tail_hasDerivAt {u : ℝ → ℂ}
    (hu : Continuous u) (hs : HasCompactSupport u) (k t : ℝ) :
    HasDerivAt (rightExponentialTail k u)
      ((k : ℂ) * rightExponentialTail k u t - u t) t := by
  obtain ⟨R, _hR, hz⟩ := exists_upper_zero hs
  have hw := weightedInput_continuous hu k
  have hJ : HasDerivAt
      (fun x : ℝ => ∫ s : ℝ in x..R, weightedInput k u s)
      (-weightedInput k u t) t :=
    intervalIntegral.integral_hasDerivAt_left (hw.intervalIntegrable t R)
      hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt
  have hExp : HasDerivAt (fun x : ℝ => (Real.exp (k * x) : ℂ))
      ((Real.exp (k * t) * k : ℝ) : ℂ) t := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id t).const_mul k).exp).ofReal_comp
  have he : (Real.exp (k * t) : ℂ) * (Real.exp (-k * t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have hrepr : rightExponentialTail k u =
      fun x : ℝ => (Real.exp (k * x) : ℂ) * ∫ s : ℝ in x..R, weightedInput k u s :=
    funext (fun x => tail_eq_interval hu hs k R x hz)
  rw [hrepr]
  apply (hExp.mul hJ).congr_deriv
  dsimp only [weightedInput]
  rw [Complex.ofReal_mul]
  calc
    ((Real.exp (k * t) : ℂ) * (k : ℂ)) *
          (∫ s : ℝ in t..R, (Real.exp (-k * s) : ℂ) * u s) +
        (Real.exp (k * t) : ℂ) * (-((Real.exp (-k * t) : ℂ) * u t)) =
      (k : ℂ) * ((Real.exp (k * t) : ℂ) *
          ∫ s : ℝ in t..R, (Real.exp (-k * s) : ℂ) * u s) -
        ((Real.exp (k * t) : ℂ) * (Real.exp (-k * t) : ℂ)) * u t := by ring
    _ = _ := by rw [he, one_mul]

private theorem tail_continuous {u : ℝ → ℂ}
    (hu : Continuous u) (hs : HasCompactSupport u) (k : ℝ) :
    Continuous (rightExponentialTail k u) :=
  continuous_iff_continuousAt.mpr fun t => (tail_hasDerivAt hu hs k t).continuousAt

private def realPairing (u v : ℝ → ℂ) (t : ℝ) : ℝ :=
  (u t).re * (v t).re + (u t).im * (v t).im

private theorem realPairing_continuous {u v : ℝ → ℂ}
    (hu : Continuous u) (hv : Continuous v) : Continuous (realPairing u v) := by
  unfold realPairing
  fun_prop

private theorem tail_normSq_hasDerivAt {u : ℝ → ℂ}
    (hu : Continuous u) (hs : HasCompactSupport u) (k t : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.normSq (rightExponentialTail k u x))
      (2 * k * Complex.normSq (rightExponentialTail k u t) -
        2 * realPairing u (rightExponentialTail k u) t) t := by
  have hd := tail_hasDerivAt hu hs k t
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
  have hfun : (fun x : ℝ => Complex.normSq (rightExponentialTail k u x)) =
      fun x : ℝ => (rightExponentialTail k u x).re * (rightExponentialTail k u x).re +
        (rightExponentialTail k u x).im * (rightExponentialTail k u x).im := by
    funext x
    exact Complex.normSq_apply _
  rw [hfun]
  apply ((hr.mul hr).add (hi.mul hi)).congr_deriv
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, zero_add, realPairing, Complex.normSq_apply]
  ring

private theorem halfline_eq_interval {f : ℝ → ℝ} (hf : Continuous f) (R : ℝ)
    (hz : ∀ t : ℝ, R ≤ t → f t = 0) :
    (∫ t : ℝ in Ioi 0, f t) = ∫ t : ℝ in (0 : ℝ)..R, f t := by
  have hae : f =ᵐ[volume.restrict (Ioi R)] (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hz t ht.le
  have hi : Integrable f (volume.restrict (Ioi R)) :=
    (integrable_zero ℝ ℝ (volume.restrict (Ioi R))).congr hae.symm
  have hzInt : (∫ t : ℝ in Ioi R, f t) = 0 := integral_eq_zero_of_ae hae
  have he := intervalIntegral.integral_interval_add_Ioi'
    (hf.intervalIntegrable 0 R) hi
  rw [hzInt, add_zero] at he
  exact he.symm

private theorem normSq_sub_real_mul (z w : ℂ) (c : ℝ) :
    Complex.normSq (z - (c : ℂ) * w) =
      Complex.normSq z + c ^ 2 * Complex.normSq w -
        2 * c * (z.re * w.re + z.im * w.im) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, zero_add]
  ring

/-- Weighted energy balance with the actual endpoint and derivative-of-weight
charges. All real rates and coefficients are allowed on this compact core. -/
theorem right_exponential_tail_weighted_energy_balance
    (u : ℝ → ℂ) (hu : Continuous u) (hs : HasCompactSupport u)
    (w dw : ℝ → ℝ) (hw : Continuous w) (hdw : Continuous dw)
    (hwderiv : ∀ t : ℝ, 0 < t → HasDerivAt w (dw t) t)
    (k c : ℝ) :
    (∫ t : ℝ in Ioi 0,
      w t * Complex.normSq (u t - (c : ℂ) * rightExponentialTail k u t)) +
      c * (2 * k - c) *
        (∫ t : ℝ in Ioi 0, w t * Complex.normSq (rightExponentialTail k u t)) +
      c * w 0 * Complex.normSq (rightExponentialTail k u 0) +
      c * (∫ t : ℝ in Ioi 0, dw t * Complex.normSq (rightExponentialTail k u t)) =
      ∫ t : ℝ in Ioi 0, w t * Complex.normSq (u t) := by
  obtain ⟨R, hR, hz⟩ := exists_upper_zero hs
  let v : ℝ → ℂ := rightExponentialTail k u
  have hv : Continuous v := tail_continuous hu hs k
  have hvz (t : ℝ) (ht : R ≤ t) : v t = 0 := tail_zero_above k R t hz ht
  have hq : Continuous (fun t : ℝ => Complex.normSq (v t)) :=
    Complex.continuous_normSq.comp hv
  have huq : Continuous (fun t : ℝ => Complex.normSq (u t)) :=
    Complex.continuous_normSq.comp hu
  have hp : Continuous (realPairing u v) := realPairing_continuous hu hv
  have hb : Continuous (fun t : ℝ => Complex.normSq (u t - (c : ℂ) * v t)) :=
    Complex.continuous_normSq.comp (hu.sub (continuous_const.mul hv))
  have hwq : Continuous (fun t : ℝ => w t * Complex.normSq (v t)) := hw.mul hq
  have hwu : Continuous (fun t : ℝ => w t * Complex.normSq (u t)) := hw.mul huq
  have hwp : Continuous (fun t : ℝ => w t * realPairing u v t) := hw.mul hp
  have hdwq : Continuous (fun t : ℝ => dw t * Complex.normSq (v t)) := hdw.mul hq
  have hwb : Continuous (fun t : ℝ =>
      w t * Complex.normSq (u t - (c : ℂ) * v t)) := hw.mul hb
  have hiq : IntervalIntegrable (fun t : ℝ => w t * Complex.normSq (v t)) volume 0 R :=
    hwq.intervalIntegrable 0 R
  have hiu : IntervalIntegrable (fun t : ℝ => w t * Complex.normSq (u t)) volume 0 R :=
    hwu.intervalIntegrable 0 R
  have hip : IntervalIntegrable (fun t : ℝ => w t * realPairing u v t) volume 0 R :=
    hwp.intervalIntegrable 0 R
  have hid : IntervalIntegrable (fun t : ℝ => dw t * Complex.normSq (v t)) volume 0 R :=
    hdwq.intervalIntegrable 0 R
  have hDderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) :
      HasDerivAt (fun x : ℝ => w x * Complex.normSq (v x))
        (dw t * Complex.normSq (v t) +
          2 * k * (w t * Complex.normSq (v t)) -
          2 * (w t * realPairing u v t)) t := by
    apply ((hwderiv t ht.1).mul (tail_normSq_hasDerivAt hu hs k t)).congr_deriv
    ring
  have hD := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (0 : ℝ)) (b := R) hR.le hwq.continuousOn hDderiv
    (((hdwq.add (hwq.const_mul (2 * k))).sub (hwp.const_mul 2)).intervalIntegrable 0 R)
  change (∫ t : ℝ in (0 : ℝ)..R,
      dw t * Complex.normSq (v t) + 2 * k * (w t * Complex.normSq (v t)) -
        2 * (w t * realPairing u v t)) =
      w R * Complex.normSq (v R) - w 0 * Complex.normSq (v 0) at hD
  rw [hvz R le_rfl, Complex.normSq_zero, mul_zero, zero_sub,
    intervalIntegral.integral_sub (hid.add (hiq.const_mul (2 * k))) (hip.const_mul 2),
    intervalIntegral.integral_add hid (hiq.const_mul (2 * k)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hD
  have hExpand :
      (∫ t : ℝ in (0 : ℝ)..R,
        w t * Complex.normSq (u t - (c : ℂ) * v t)) =
      (∫ t : ℝ in (0 : ℝ)..R, w t * Complex.normSq (u t)) +
        c ^ 2 * (∫ t : ℝ in (0 : ℝ)..R, w t * Complex.normSq (v t)) -
        2 * c * (∫ t : ℝ in (0 : ℝ)..R, w t * realPairing u v t) := by
    calc
      _ = ∫ t : ℝ in (0 : ℝ)..R,
          w t * Complex.normSq (u t) + c ^ 2 * (w t * Complex.normSq (v t)) -
            2 * c * (w t * realPairing u v t) := by
        apply intervalIntegral.integral_congr
        intro t _
        change w t * Complex.normSq (u t - (c : ℂ) * v t) =
          w t * Complex.normSq (u t) + c ^ 2 * (w t * Complex.normSq (v t)) -
            2 * c * (w t * realPairing u v t)
        rw [normSq_sub_real_mul]
        dsimp only [realPairing]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hiu.add (hiq.const_mul (c ^ 2)))
            (hip.const_mul (2 * c)),
          intervalIntegral.integral_add hiu (hiq.const_mul (c ^ 2)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  change (∫ t : ℝ in Ioi 0, w t * Complex.normSq (u t - (c : ℂ) * v t)) +
      c * (2 * k - c) * (∫ t : ℝ in Ioi 0, w t * Complex.normSq (v t)) +
      c * w 0 * Complex.normSq (v 0) +
      c * (∫ t : ℝ in Ioi 0, dw t * Complex.normSq (v t)) =
      ∫ t : ℝ in Ioi 0, w t * Complex.normSq (u t)
  rw [halfline_eq_interval hwb R (fun t ht => by
        simp only [hz t ht, hvz t ht, mul_zero, sub_self, Complex.normSq_zero]),
    halfline_eq_interval hwq R (fun t ht => by
        simp only [hvz t ht, Complex.normSq_zero, mul_zero]),
    halfline_eq_interval hdwq R (fun t ht => by
        simp only [hvz t ht, Complex.normSq_zero, mul_zero]),
    halfline_eq_interval hwu R (fun t ht => by
        simp only [hz t ht, Complex.normSq_zero, mul_zero]),
    hExpand]
  linear_combination c * hD

/-- The exact half-line norm balance of the actual exponential-tail map.
All scalar parameters are real. Compact support makes the half-line integrals
finite even when the rate is nonpositive. The boundary term is the actual tail
value at zero; no zero-boundary condition or Fourier-domain assumption occurs. -/
theorem right_exponential_tail_energy_balance
    (u : ℝ → ℂ) (hu : Continuous u) (hs : HasCompactSupport u) (k c : ℝ) :
    (∫ t : ℝ in Ioi 0,
      Complex.normSq (u t - (c : ℂ) * rightExponentialTail k u t)) +
      c * (2 * k - c) *
        (∫ t : ℝ in Ioi 0, Complex.normSq (rightExponentialTail k u t)) +
      c * Complex.normSq (rightExponentialTail k u 0) =
      ∫ t : ℝ in Ioi 0, Complex.normSq (u t) := by
  simpa only [one_mul, mul_one, zero_mul, integral_zero, mul_zero, add_zero] using
    right_exponential_tail_weighted_energy_balance u hu hs
      (fun _ : ℝ => (1 : ℝ)) (fun _ : ℝ => (0 : ℝ))
      continuous_const continuous_const
      (fun t _ => hasDerivAt_const t (1 : ℝ)) k c

#print axioms right_exponential_tail_energy_balance
#print axioms right_exponential_tail_weighted_energy_balance

end D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

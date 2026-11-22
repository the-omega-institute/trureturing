/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffUniformWidth
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffUniformWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier recovery at even cutoffs with error uniform in every positive logarithmic width. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoffFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean (frequency)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

private theorem width_multiplier_bound {s L : ℝ} (hs : 0 < s) (hL : 0 < L) (ω : ℝ) :
    ‖(Complex.exp (((-(s : ℂ)) + (ω : ℂ)*Complex.I)*(L : ℂ))-1) /
      ((1-Real.exp (-s*L) : ℝ) : ℂ)‖ ≤ 1 + |ω| / s := by
  let t := Real.exp (-s*L)
  let v := Complex.exp (Complex.I*((ω*L : ℝ) : ℂ))
  have ht : 0 < t := Real.exp_pos _
  have hd : 0 < 1-t := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) hL))
  have he : Complex.exp (((-(s : ℂ)) + (ω : ℂ)*Complex.I)*(L : ℂ)) = (t : ℂ)*v := by
    dsimp only [t, v]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hwidth : t*L/(1-t) ≤ 1/s := by
    have hi : t*Real.exp (s*L) = 1 := by
      dsimp only [t]
      rw [← Real.exp_add, show -s*L+s*L = 0 by ring, Real.exp_zero]
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s*L)) ht.le
    rw [hi] at h
    rw [div_le_div_iff₀ hd hs]
    linarith only [show t*L*s+t = t*(s*L+1) by ring, h]
  have hnorm : ‖v - 1‖ ≤ |ω| * L := by
    simpa only [v, Real.norm_eq_abs, abs_mul, abs_of_pos hL] using
      Real.norm_exp_I_mul_ofReal_sub_one_le (x := ω*L)
  have hsplit : ‖(t : ℂ)*v-1‖ ≤ t*(|ω| * L)+(1-t) := by
    rw [show (t : ℂ)*v-1 = (t : ℂ)*(v-1) - ((1-t : ℝ) : ℂ) by push_cast; ring]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, Real.norm_of_nonneg hd.le]
    exact add_le_add_left (mul_le_mul_of_nonneg_left hnorm ht.le) _
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  refine (div_le_div_of_nonneg_right hsplit hd.le).trans ?_
  rw [add_div, div_self hd.ne']
  have h := mul_le_mul_of_nonneg_left hwidth (abs_nonneg ω)
  calc
    _ = 1 + |ω| * (t*L/(1-t)) := by ring
    _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using add_le_add_right h 1

private theorem width_coefficient_uniform_bound (hRH : RiemannHypothesis) {r L : ℝ}
    (hr : 1 < r) (hL : 0 < L) (k : ℕ) :
    let s : ℝ := 1/2-(2*r)⁻¹
    ‖windowCoefficient r L (actualZero k)‖ ≤ (r * ‖actualCoeff k‖) * (r + 1/s) := by
  let s : ℝ := 1/2-(2*r)⁻¹
  let v := frequency k/(r : ℂ)
  let a := rootCoeff r k
  let e := rootExponent r k
  let ω := (actualZero k).im/r
  have hr₀ : 0 < r := by linarith
  have hs : 0 < s := by
    dsimp only [s]
    rw [show (1 : ℝ)/2 = 2⁻¹ by norm_num]
    exact sub_pos.mpr (inv_strictAnti₀ (by norm_num) (show 2 < 2*r by linarith))
  have hz : IsNontrivialZero (actualZero k) :=
    actualData.zero_isNontrivial (actualOccurrenceEquiv k).1
  have hv : v = (ω : ℂ)*Complex.I := window_mode_eq_ordinate hRH hr₀ hz
  have he : e.im = ω := by
    simp [e, ω, rootExponent, Complex.div_im, Complex.normSq_ofReal]
    field_simp [hr₀.ne']
  have hnorm : |ω| ≤ ‖e‖ := he ▸ Complex.abs_im_le_norm e
  have hnorme : 0 < ‖e‖ := (inv_pos.mpr hr₀).trans_le (rootExponent_norm hr k)
  rw [window_coefficient_of_occurrence hr L k]
  change ‖a/e * ((Complex.exp ((-(s : ℂ)+v)*(L : ℂ))-1)/_)‖ ≤ _
  rw [hv, norm_mul]
  have h := width_multiplier_bound hs hL ω
  calc
    _ ≤ ‖a/e‖ * (1 + |ω|/s) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = ‖a/e‖ + (‖a/e‖ * |ω|)/s := by ring
    _ ≤ (r * ‖actualCoeff k‖) * r + (r * ‖actualCoeff k‖)/s := by
      refine add_le_add (root_primitive_coefficient_norm_le hr k)
        (div_le_div_of_nonneg_right ?_ hs.le)
      calc
        _ ≤ ‖a/e‖ * ‖e‖ := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
        _ = ‖a‖ := by rw [norm_div, div_mul_cancel₀ _ hnorme.ne']
        _ ≤ _ := rootCoeff_bound hr k
    _ = _ := by ring

theorem signed_window_even_cutoff_fourier_uniform_width (hRH : RiemannHypothesis) :
    ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ m r : ℕ, 2 ≤ m → m+1 = 2*r →
      let s := orderRate m
      let c := (μ (m+1) : ℝ)*(((m : ℝ)+1)/((m : ℝ)*s))
      let target := fun L ω : ℝ => (if ω=0 then -(c : ℂ) else 0) - (μ r : ℂ) *
        (∑' k, if windowMode (r : ℝ) (actualZero k) = (ω : ℂ)*Complex.I
          then windowCoefficient (r : ℝ) L (actualZero k) else 0)
      (∀ ω : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ U T : ℝ, U₀ ≤ U → 0 < T →
        let F := fun u : ℝ => ((signedWindowResidual m (Real.exp u) (Real.exp (u+L)) /
          powerGap s (Real.exp u) (Real.exp (u+L)) : ℝ) : ℂ) *
            Complex.exp (-((ω : ℂ)*Complex.I)*(u : ℂ))
        IntervalIntegrable F volume U (U+T) ∧
        ‖(∫ u in U..U+T, F u)/(T : ℂ)-target L ω‖ ≤ C/T) ∧
      ∀ L : ℝ, 0 < L → target L 0 = -(c : ℂ) ∧
        ∀ z : ℂ, IsNontrivialZero z →
          target L (z.im/(r : ℝ)) =
            -(μ r : ℂ) * (Zeta23.zeroMult z : ℂ) * windowCoefficient (r : ℝ) L z ∧
          windowCoefficient (r : ℝ) L z ≠ 0 := by
  obtain ⟨U₀, hU₀, hbound⟩ := signed_window_even_cutoff_fourier_bound hRH
  obtain ⟨_, _, hspec⟩ := signed_window_even_cutoff_fourier hRH
  refine ⟨U₀, hU₀, fun m r hm heven => ⟨?_, fun L hL => (hspec m r hm heven L hL).2⟩⟩
  intro ω
  obtain ⟨A, B, hA, hB, h⟩ := hbound m r hm heven ω
  let s := orderRate m
  let M (k : ℕ) := ((r : ℝ)*‖actualCoeff k‖)*((r : ℝ)+1/s)
  have hr : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hq : (m : ℝ)+1 = 2*(r : ℝ) := by exact_mod_cast heven
  have hs : s = 1/2-(2*(r : ℝ))⁻¹ := by dsimp [s, orderRate]; rw [hq]
  have hmajorant (L : ℝ) (hL : 0 < L) (k : ℕ) :
      ‖windowCoefficient (r : ℝ) L (actualZero k)‖ ≤ M k := by
    simpa only [M, hs] using width_coefficient_uniform_bound hRH hr hL k
  have hM : Summable M :=
    (actualCoeff_hasSum.summable.norm.mul_left (r : ℝ)).mul_right ((r : ℝ)+1/s)
  have hM₀ (k : ℕ) : 0 ≤ M k := (norm_nonneg _).trans (hmajorant 1 zero_lt_one k)
  refine ⟨A+B*(∑' k, M k), add_pos_of_pos_of_nonneg hA
    (mul_nonneg hB (tsum_nonneg hM₀)), fun L hL U T hU hT => ?_⟩
  have hsum := hM.of_nonneg_of_le (fun k => norm_nonneg (windowCoefficient (r : ℝ) L (actualZero k)))
    (hmajorant L hL)
  obtain ⟨hi, hb⟩ := h L hL U T hU hT
  refine ⟨hi, hb.trans (div_le_div_of_nonneg_right ?_ hT.le)⟩
  exact add_le_add_right (mul_le_mul_of_nonneg_left (hsum.tsum_le_tsum (hmajorant L hL) hM) hB) A

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

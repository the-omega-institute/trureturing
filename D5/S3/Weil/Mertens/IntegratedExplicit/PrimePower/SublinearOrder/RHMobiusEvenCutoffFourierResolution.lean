/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourierResolution
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourierResolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-length frequency resolution of the normalized signed even-cutoff prime window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoffUniformWidth
import D5.S3.Arith.Robin.ForwardKernel.WeightedPrimitiveBound
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Set MeasureTheory
open D5.S3.Arith.Robin.ForwardKernel.WeightedPrimitiveBound

private theorem complex_weighted_integral_le_of_primitive_bound
    {f W W' : ℝ → ℂ} {A B K D : ℝ}
    (hAB : A ≤ B) (hf : IntervalIntegrable f volume A B)
    (hW : ContDiff ℝ 1 W) (hW' : Continuous W')
    (hderiv : ∀ x : ℝ, HasDerivAt W (W' x) x)
    (hK : 0 ≤ K) (hsize : ‖W B‖ ≤ 1) (hvar : ∀ x : ℝ, ‖W' x‖ ≤ D)
    (hF : ∀ y ∈ Icc A B, ‖∫ x in A..y, f x‖ ≤ K) :
    IntervalIntegrable (fun x => W x * f x) volume A B ∧
      ‖∫ x in A..B, W x * f x‖ ≤ 4*K*(1+(B-A)*D) := by
  have hprod := hf.continuousOn_mul hW.continuous.continuousOn
  refine ⟨hprod, ?_⟩
  have scalar (p q : ℂ →L[ℝ] ℝ) (hp : ∀ z, |p z| ≤ ‖z‖)
      (hq : ∀ z, |q z| ≤ ‖z‖) : |∫ x in A..B, p (W x) * q (f x)| ≤
        K*(1+(B-A)*D) := by
    have hqf (y : ℝ) (hy : y ∈ Icc A B) : IntervalIntegrable (fun x => q (f x)) volume A y := by
      have hfy := hf.mono_set (show uIcc A y ⊆ uIcc A B by
        rw [uIcc_of_le hy.1, uIcc_of_le hAB]
        exact Icc_subset_Icc_right hy.2)
      exact ⟨q.integrable_comp hfy.1, q.integrable_comp hfy.2⟩
    have hprimitive (y : ℝ) (hy : y ∈ Icc A B) : |∫ x in A..y, q (f x)| ≤ K := by
      have hfy := hf.mono_set (show uIcc A y ⊆ uIcc A B by
        rw [uIcc_of_le hy.1, uIcc_of_le hAB]
        exact Icc_subset_Icc_right hy.2)
      rw [q.intervalIntegral_comp_comm hfy]
      exact (hq _).trans (hF y hy)
    have hP : ContDiff ℝ 1 (fun x => p (W x)) := p.contDiff.comp hW
    have hd : ∀ x, deriv (fun y => p (W y)) x = p (W' x) :=
      fun x => (p.hasFDerivAt.comp_hasDerivAt x (hderiv x)).deriv
    refine (weighted_integral_le_of_primitive_bound hAB (hqf B ⟨hAB, le_rfl⟩)
      hP.contDiffOn hK hprimitive).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK
    apply add_le_add ((hp _).trans hsize)
    simp_rw [hd]
    rw [show (B-A)*D = (∫ _ in A..B, D) by rw [intervalIntegral.integral_const, smul_eq_mul]]
    apply intervalIntegral.integral_mono_on hAB
    · exact (p.continuous.comp hW').abs.intervalIntegrable _ _
    · exact intervalIntegrable_const
    · exact fun x _ => (hp _).trans (hvar x)
  have hfr : IntervalIntegrable (fun x => (f x).re) volume A B :=
    ⟨Complex.reCLM.integrable_comp hf.1, Complex.reCLM.integrable_comp hf.2⟩
  have hfi : IntervalIntegrable (fun x => (f x).im) volume A B :=
    ⟨Complex.imCLM.integrable_comp hf.1, Complex.imCLM.integrable_comp hf.2⟩
  have hr : |(∫ x in A..B, W x * f x).re| ≤ 2*(K*(1+(B-A)*D)) := by
    change |Complex.reCLM (∫ x in A..B, W x * f x)| ≤ _
    rw [← Complex.reCLM.intervalIntegral_comp_comm hprod]
    change |∫ x in A..B, (W x * f x).re| ≤ _
    simp_rw [Complex.mul_re]
    rw [intervalIntegral.integral_sub
      (hfr.continuousOn_mul (show ContinuousOn (fun x => (W x).re) (uIcc A B) from
        (Complex.continuous_re.comp hW.continuous).continuousOn))
      (hfi.continuousOn_mul (show ContinuousOn (fun x => (W x).im) (uIcc A B) from
        (Complex.continuous_im.comp hW.continuous).continuousOn))]
    refine (abs_sub _ _).trans ?_
    have hrr := scalar Complex.reCLM Complex.reCLM Complex.abs_re_le_norm Complex.abs_re_le_norm
    have hii := scalar Complex.imCLM Complex.imCLM Complex.abs_im_le_norm Complex.abs_im_le_norm
    simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hrr hii
    linarith only [hrr, hii]
  have hi : |(∫ x in A..B, W x * f x).im| ≤ 2*(K*(1+(B-A)*D)) := by
    change |Complex.imCLM (∫ x in A..B, W x * f x)| ≤ _
    rw [← Complex.imCLM.intervalIntegral_comp_comm hprod]
    change |∫ x in A..B, (W x * f x).im| ≤ _
    simp_rw [Complex.mul_im]
    rw [intervalIntegral.integral_add
      (hfi.continuousOn_mul (show ContinuousOn (fun x => (W x).re) (uIcc A B) from
        (Complex.continuous_re.comp hW.continuous).continuousOn))
      (hfr.continuousOn_mul (show ContinuousOn (fun x => (W x).im) (uIcc A B) from
        (Complex.continuous_im.comp hW.continuous).continuousOn))]
    refine (abs_add_le _ _).trans ?_
    have hri := scalar Complex.reCLM Complex.imCLM Complex.abs_re_le_norm Complex.abs_im_le_norm
    have hir := scalar Complex.imCLM Complex.reCLM Complex.abs_im_le_norm Complex.abs_re_le_norm
    simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hri hir
    linarith only [hri, hir]
  calc
    _ ≤ _ := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := add_le_add hr hi
    _ = _ := by ring


private theorem detuned_average_of_prefix_bound {U T C : ℝ} (hT : 0 < T) (hC : 0 ≤ C)
    (f : ℝ → ℂ) (a : ℂ) (v : ℝ)
    (havg : ∀ S : ℝ, 0 < S → IntervalIntegrable f volume U (U+S) ∧
      ‖(∫ u in U..U+S, f u)/(S : ℂ)-a‖ ≤ C/S) :
    let K := fun t : ℝ => Complex.exp (-(v : ℂ)*Complex.I*(t : ℂ))
    let W := fun u : ℝ => K ((u-U)/T)
    IntervalIntegrable (fun u => f u*W u) volume U (U+T) ∧
      ‖(∫ u in U..U+T, f u*W u)/(T : ℂ)-a*(∫ t in (0 : ℝ)..1, K t)‖ ≤
        4*C*(1+|v|)/T := by
  let K (t : ℝ) := Complex.exp (-(v : ℂ)*Complex.I*(t : ℂ))
  let W (u : ℝ) := K ((u-U)/T)
  let d : ℂ := (-((v/T : ℝ) : ℂ))*Complex.I
  let G (u : ℝ) := f u-a
  have hUT : U ≤ U+T := by linarith
  have hf := (havg T hT).1
  have hG : IntervalIntegrable G volume U (U+T) := hf.sub intervalIntegrable_const
  have hW : ContDiff ℝ 1 W := by
    have harg : ContDiff ℝ 1 (fun u : ℝ => (u-U)/T) := by fun_prop
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp harg)).cexp
  have hd (u : ℝ) : HasDerivAt W (d*W u) u := by
    have harg : HasDerivAt (fun x : ℝ => (x-U)/T) (1/T) u := by
      simpa using ((hasDerivAt_id u).sub_const U).div_const T
    have h := (harg.ofReal_comp.const_mul (-(v : ℂ)*Complex.I)).cexp
    convert h using 1
    simp [W, K, d, Complex.ofReal_div]
    ring
  have hunit (u : ℝ) : ‖W u‖ = 1 := by
    simp [W, K, Complex.norm_exp, Complex.mul_re]
  have hvar (u : ℝ) : ‖d*W u‖ ≤ |v|/T := by
    rw [norm_mul, hunit, mul_one]
    simp [d, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  have hprefix (y : ℝ) (hy : y ∈ Icc U (U+T)) : ‖∫ u in U..y, G u‖ ≤ C := by
    rcases hy.1.eq_or_lt with heq | hlt
    · rw [← heq, intervalIntegral.integral_same, norm_zero]
      exact hC
    have hS : 0 < y-U := sub_pos.mpr hlt
    have hS' : (↑(y-U) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
    obtain ⟨hi,hb⟩ := havg (y-U) hS
    rw [show U+(y-U) = y by ring] at hi hb
    unfold G
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const, intervalIntegral.integral_const,
      Complex.real_smul]
    rw [show (∫ u in U..y, f u)/(↑(y-U) : ℂ) - a =
        ((∫ u in U..y, f u) - (↑(y-U) : ℂ)*a)/(↑(y-U) : ℂ) by field_simp [hS'],
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS] at hb
    exact (div_le_div_iff_of_pos_right hS).mp hb
  obtain ⟨hweighted, hb⟩ := complex_weighted_integral_le_of_primitive_bound hUT hG hW
    (hW.continuous.const_mul d) hd hC (hunit _).le hvar hprefix
  have hspan : (U+T-U)*(|v|/T) = |v| := by
    rw [show U+T-U = T by ring]
    field_simp
  rw [hspan] at hb
  have hWint : (∫ u in U..U+T, W u) = (T : ℂ)*(∫ t in (0 : ℝ)..1, K t) := by
    change (∫ u in U..U+T, K ((u-U)/T)) = _
    simp_rw [sub_div]
    rw [intervalIntegral.integral_comp_div_sub K hT.ne', sub_self,
      show (U+T)/T-U/T = 1 by rw [add_div, div_self hT.ne']; ring, Complex.real_smul]
  have hwint := hW.continuous.intervalIntegrable (μ := volume) U (U+T)
  have hfW := hf.mul_continuousOn hW.continuous.continuousOn
  have hsplit : (∫ u in U..U+T, W u * G u) =
      (∫ u in U..U+T, f u * W u) - (T : ℂ)*(a*(∫ t in (0 : ℝ)..1, K t)) := by
    simp_rw [G, mul_sub, mul_comm (W _)]
    rw [intervalIntegral.integral_sub hfW (hwint.const_mul a), intervalIntegral.integral_const_mul,
      hWint]
    ring
  change IntervalIntegrable (fun u => f u*W u) volume U (U+T) ∧ _
  refine ⟨hfW, ?_⟩
  rw [hsplit] at hb
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  change ‖(∫ u in U..U+T, f u*W u)/(T : ℂ)-a*(∫ t in (0 : ℝ)..1, K t)‖ ≤ _
  rw [show (∫ u in U..U+T, f u*W u)/(T : ℂ)-a*(∫ t in (0 : ℝ)..1, K t) =
    ((∫ u in U..U+T, f u*W u)-(T : ℂ)*(a*(∫ t in (0 : ℝ)..1, K t)))/(T : ℂ) by
      field_simp [hT'], norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  exact div_le_div_of_nonneg_right hb hT.le


open ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

/-- A frequency offset of order one over the averaging length has the unit-interval response. -/
theorem signed_window_even_cutoff_detuned_fourier (hRH : RiemannHypothesis) :
    ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ m r : ℕ, 2 ≤ m → m+1 = 2*r →
      let s := orderRate m
      let c := (μ (m+1) : ℝ)*(((m : ℝ)+1)/((m : ℝ)*s))
      let target := fun L ω : ℝ => (if ω=0 then -(c : ℂ) else 0) - (μ r : ℂ) *
        (∑' k, if windowMode (r : ℝ) (actualZero k) = (ω : ℂ)*Complex.I
          then windowCoefficient (r : ℝ) L (actualZero k) else 0)
      (∀ ω : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ U T : ℝ, U₀ ≤ U → 0 < T →
        ∀ R v : ℝ, 0 ≤ R → |v| ≤ R →
        let F := fun u : ℝ => ((signedWindowResidual m (Real.exp u) (Real.exp (u+L)) /
          powerGap s (Real.exp u) (Real.exp (u+L)) : ℝ) : ℂ) *
            Complex.exp (-((ω : ℂ)*Complex.I)*(u : ℂ))
        let K := fun t : ℝ => Complex.exp (-(v : ℂ)*Complex.I*(t : ℂ))
        IntervalIntegrable (fun u => F u*K ((u-U)/T)) volume U (U+T) ∧
        ‖(∫ u in U..U+T, F u*K ((u-U)/T))/(T : ℂ)-
          target L ω*(∫ t in (0 : ℝ)..1, K t)‖ ≤ C*(1+R)/T) ∧
      ∀ L : ℝ, 0 < L → target L 0 = -(c : ℂ) ∧
        ∀ z : ℂ, IsNontrivialZero z →
          target L (z.im/(r : ℝ)) =
            -(μ r : ℂ) * (Zeta23.zeroMult z : ℂ) * windowCoefficient (r : ℝ) L z ∧
          windowCoefficient (r : ℝ) L z ≠ 0 := by
  obtain ⟨U₀, hU₀, h⟩ := signed_window_even_cutoff_fourier_uniform_width hRH
  refine ⟨U₀, hU₀, fun m r hm heven => ?_⟩
  obtain ⟨hav, hspec⟩ := h m r hm heven
  refine ⟨?_, hspec⟩
  intro ω
  obtain ⟨C, hC, hb⟩ := hav ω
  refine ⟨4*C, by positivity, fun L hL U T hU hT R v _hv hRv => ?_⟩
  obtain ⟨hi, htest⟩ := detuned_average_of_prefix_bound hT hC.le _ _ v (hb L hL U · hU ·)
  refine ⟨hi, htest.trans ?_⟩
  gcongr


end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

/- GID: D5/S3/Weil/ZetaBridge/OriginalIocFourierEvaluation
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaBridge/OriginalIocFourierEvaluation
   mirror-E: none(waiver:infinite-dimensional-analytic-identity)
   anchors: []
   utility: none
   digest: Evaluate the literal interval Fourier transform by the complete complex L2 basis. -/

import D5.S3.Weil.ZetaBridge.OriginalIocFourierMass
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open scoped BigOperators ComplexConjugate InnerProductSpace
open Complex MeasureTheory Set Zeta23

noncomputable section
namespace D5.S3.Weil.ZetaBridge.OriginalIocFourier

/-- The bounded test kernel for the PLUS paper transform. Its conjugate is
exactly the exponential in the integral; it imposes no boundary condition. -/
def evaluationKernel (t x : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))

private theorem evaluationKernel_memLp (a b t : ℝ) :
    MemLp (evaluationKernel t) 2 (volume.restrict (Ioc a b)) := by
  apply MemLp.of_bound
    (show Continuous (evaluationKernel t) by unfold evaluationKernel; fun_prop).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x ↦ by
    simp [evaluationKernel, Complex.norm_exp, Complex.mul_re, Complex.mul_im])

/-- Original interval pairing, with the normalized Haar factor displayed.
Only the first argument is lifted; the second can be any L2 representative. -/
private theorem inner_liftIoc_right {T : ℝ} [Fact (0 < T)] {a : ℝ} {k : ℝ → ℂ}
    (hk : MemLp (AddCircle.liftIoc T a k) 2 AddCircle.haarAddCircle)
    (Y : Lp ℂ 2 (AddCircle.haarAddCircle (T := T)))
    (g : AddCircle T → ℂ) (hY : Y =ᵐ[AddCircle.haarAddCircle] g) :
    ⟪hk.toLp (AddCircle.liftIoc T a k), Y⟫_ℂ = (T⁻¹ : ℝ) •
      ∫ x in a..a + T, conj (k x) * g (x : AddCircle T) := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply']
  rw [integral_congr_ae (show
      (fun x ↦ conj (hk.toLp (AddCircle.liftIoc T a k) x) * Y x) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ conj (AddCircle.liftIoc T a k x) * g x) from by
        filter_upwards [hk.coeFn_toLp, hY] with x hx hy
        rw [hx, hy])]
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage T a]
  congr 1
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall (fun x hx ↦ ?_)
  rw [uIoc_of_le (by linarith [Fact.out (p := 0 < T)])] at hx
  rw [AddCircle.liftIoc_coe_apply hx]

private theorem phase_mul_self (n : ℤ) : phase n * phase n = 1 := by
  simp only [phase, ← mul_zpow, neg_one_mul, neg_neg, one_zpow]

/-- The original zero-extension has its literal PLUS-transform interval integral.
This is an integral identity, including for arbitrary measurable representatives. -/
theorem paperFT_iocZeroExtend {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) (t : ℝ) :
    paperFT (iocZeroExtend L f) t =
      ∫ x in (-L / 2)..(L / 2),
        f x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
  rw [paperFT_def]
  have hprod : (fun x ↦ iocZeroExtend L f x *
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) =
      (interval L).indicator (fun x ↦ f x *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) := by
    funext x
    exact (Set.indicator_mul_left (interval L) f
      (fun x ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))).symm
  rw [hprod]
  unfold interval
  rw [integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (by linarith : -L / 2 ≤ L / 2)]

/-- The named signed coefficient is the actual conjugate-first coefficient
of the literal phase-adjusted basis on the original dx interval. -/
theorem signedCoeff_eq_integral {L : ℝ} (hL : 0 < L) (f : ℝ → ℂ) (n : ℤ) :
    signedCoeff L hL f n =
      ∫ x in (-L / 2)..(L / 2), conj (signedBasis L n x) * f x := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hlen : L / 2 - -L / 2 = L := by ring
  have hs0 : (Real.sqrt L : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hL)
  have hs : (Real.sqrt L : ℂ) ^ 2 = (L : ℂ) := by
    exact_mod_cast Real.sq_sqrt hL.le
  have hL0 : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hphase : conj (phase n) = phase n := by simp [phase]
  have hb : (∫ x in (-L / 2)..(L / 2), conj (signedBasis L n x) * f x) =
      phase n * (Real.sqrt L : ℂ)⁻¹ *
        ∫ x in (-L / 2)..(L / 2),
          fourier (-n) (x : AddCircle L) * f x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx ↦ ?_)
    rw [uIoc_of_le (by linarith : -L / 2 ≤ L / 2)] at hx
    rw [signedBasis, iocZeroExtend_eq_on_mem hx]
    have he : conj (Complex.exp (Complex.I * (frequency L n : ℂ) * (x : ℂ))) =
        fourier (-n) (x : AddCircle L) := by
      rw [← Complex.exp_conj, fourier_coe_apply]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Int.cast_neg]
      dsimp [frequency]
      push_cast
      ring
    simp only [map_mul, map_inv₀, hphase, Complex.conj_ofReal, he]
    ring
  rw [hb, signedCoeff, fourierCoeffOn_eq_integral, hlen]
  simp only [smul_eq_mul, real_smul, one_div, Complex.ofReal_inv]
  rw [← hs]
  field_simp [hs0, hL0]
  <;> ring

/-- The literal defining integral exists absolutely for every real frequency. -/
theorem integrable_paperFT_integrand {L : ℝ} {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (interval L))) (t : ℝ) :
    Integrable (fun x ↦ iocZeroExtend L f x *
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) := by
  letI : IsFiniteMeasure (volume.restrict (interval L)) := by
    unfold interval
    infer_instance
  have hfi : Integrable f (volume.restrict (interval L)) := hf.integrable (by norm_num)
  have hp : Integrable
      (fun x ↦ f x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))
      (volume.restrict (interval L)) := by
    apply hfi.mul_bdd (c := 1)
    · exact (show Continuous (fun x : ℝ ↦
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) by fun_prop).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x ↦ by
        simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im])
  have hi := (integrable_indicator_iff
    (by exact measurableSet_Ioc : MeasurableSet (interval L))).mpr hp
  convert hi using 1
  funext x
  exact (Set.indicator_mul_left (interval L) f
    (fun x ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))).symm

/-- Bounded Fourier evaluation of every original Ioc L2 function. This is the
Hilbert-space expansion of an integral pairing, not pointwise inversion. -/
theorem hasSum_signedCoeff_mul_basisPaperFT {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (interval L))) (t : ℝ) :
    HasSum (fun n : ℤ ↦ signedCoeff L hL f n * basisPaperFT L n t)
      (paperFT (iocZeroExtend L f) t) := by
  letI : Fact (0 < L) := ⟨hL⟩
  have hend : -L / 2 + L = L / 2 := by ring
  have hf' : MemLp f 2 (volume.restrict (Ioc (-L / 2) (-L / 2 + L))) := by
    simpa only [hend, interval] using hf
  let hF := hf'.memLp_liftIoc.haarAddCircle
  let hK := (evaluationKernel_memLp (-L / 2) (-L / 2 + L) t).memLp_liftIoc.haarAddCircle
  let F := hF.toLp (AddCircle.liftIoc L (-L / 2) f)
  let K := hK.toLp (AddCircle.liftIoc L (-L / 2) (evaluationKernel t))
  have hFcoef (n : ℤ) : ⟪fourierBasis n, F⟫_ℂ =
      fourierCoeffOn (interval_left_lt_right hL) f n := by
    rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr,
      fourierCoeff_congr_ae hF.coeFn_toLp]
    simpa only [hend] using (fourierCoeff_liftIoc_eq (T := L) (a := -L / 2) f n)
  have hKbasis (n : ℤ) : ⟪K, fourierBasis n⟫_ℂ =
      (L⁻¹ : ℝ) • (∫ x in (-L / 2)..(L / 2),
        Complex.exp (Complex.I * ((t + frequency L n : ℝ) : ℂ) * (x : ℂ))) := by
    rw [coe_fourierBasis]
    rw [inner_liftIoc_right hK _ (fourier n) (coeFn_fourierLp 2 n)]
    rw [hend]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    simp only [evaluationKernel, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I,
      Complex.conj_ofReal, neg_neg, fourier_coe_apply]
    rw [← Complex.exp_add]
    congr 1
    dsimp [frequency]
    push_cast
    ring
  have hKF : ⟪K, F⟫_ℂ = (L⁻¹ : ℝ) • paperFT (iocZeroExtend L f) t := by
    rw [inner_liftIoc_right hK F (AddCircle.liftIoc L (-L / 2) f) hF.coeFn_toLp,
      hend, paperFT_iocZeroExtend hL]
    congr 1
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx ↦ ?_)
    rw [uIoc_of_le (by linarith : -L / 2 ≤ L / 2)] at hx
    rw [AddCircle.liftIoc_coe_apply (by simpa only [hend] using hx)]
    simp only [evaluationKernel, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_I,
      Complex.conj_ofReal, neg_neg, mul_comm]
  have h := (fourierBasis.hasSum_inner_mul_inner K F).mul_left (L : ℂ)
  simp_rw [hFcoef, hKbasis, hKF, real_smul, Complex.ofReal_inv] at h
  have hL0 : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hterm (n : ℤ) : signedCoeff L hL f n * basisPaperFT L n t =
      (L : ℂ) * ((L : ℂ)⁻¹ *
        (∫ x in (-L / 2)..(L / 2),
          Complex.exp (Complex.I * ((t + frequency L n : ℝ) : ℂ) * (x : ℂ))) *
        fourierCoeffOn (interval_left_lt_right hL) f n) := by
    rw [basisPaperFT_eq_centered hL]
    dsimp [signedCoeff]
    have hsqrt : (Real.sqrt L : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hL)
    calc
      _ = (phase n * phase n) *
          ((Real.sqrt L : ℂ) * (Real.sqrt L : ℂ)⁻¹) *
          (fourierCoeffOn (interval_left_lt_right hL) f n *
            (∫ x in (-L / 2)..(L / 2),
              Complex.exp (Complex.I * ((t + frequency L n : ℝ) : ℂ) * (x : ℂ)))) := by ring
      _ = _ := by
        rw [phase_mul_self, mul_inv_cancel₀ hsqrt]
        field_simp [hL0]
        <;> ring
  simpa only [← hterm, mul_inv_cancel_left₀ hL0] using h

#print axioms hasSum_signedCoeff_mul_basisPaperFT

end D5.S3.Weil.ZetaBridge.OriginalIocFourier

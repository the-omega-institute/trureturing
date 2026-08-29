/- GID: D5/S3/Weil/ZetaGamma/PoleContinuumCompletion
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/PoleContinuumCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the pole-continuum Green kernel and its exact digamma shift. -/

import D5.S3.Weil.PrimePoleTerms
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace D5.S3.Weil.ZetaGamma.PoleContinuumCompletion

open MeasureTheory Set
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open scoped ComplexConjugate

noncomputable section

private theorem pole_term_eq_decaying_add_growing (f : WeilTestFunction) :
    poleTerm (convolutionSquare f) =
      (∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * convolutionSquare f u) +
        ∫ u : ℝ, (Real.exp (|u| / 2) : ℂ) * convolutionSquare f u := by
  let g : WeilTestFunction := convolutionSquare f
  have hDecay : Integrable (fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) * g u) :=
    ((by fun_prop : Continuous fun u : ℝ => (Real.exp (-|u| / 2) : ℂ)).mul
      g.continuous).integrable_of_hasCompactSupport g.hasCompactSupport.mul_left
  have hGrow : Integrable (fun u : ℝ => (Real.exp (|u| / 2) : ℂ) * g u) :=
    ((by fun_prop : Continuous fun u : ℝ => (Real.exp (|u| / 2) : ℂ)).mul
      g.continuous).integrable_of_hasCompactSupport g.hasCompactSupport.mul_left
  have hMinus : Integrable
      (fun u : ℝ => Complex.exp (-Complex.I * (-Complex.I / 2) * (u : ℂ)) * g u) :=
    ((by fun_prop : Continuous fun u : ℝ =>
      Complex.exp (-Complex.I * (-Complex.I / 2) * (u : ℂ))).mul
      g.continuous).integrable_of_hasCompactSupport g.hasCompactSupport.mul_left
  have hPlus : Integrable
      (fun u : ℝ => Complex.exp (-Complex.I * (Complex.I / 2) * (u : ℂ)) * g u) :=
    ((by fun_prop : Continuous fun u : ℝ =>
      Complex.exp (-Complex.I * (Complex.I / 2) * (u : ℂ))).mul
      g.continuous).integrable_of_hasCompactSupport g.hasCompactSupport.mul_left
  rw [poleTerm, fourierLaplace_apply, fourierLaplace_apply,
    ← integral_add hMinus hPlus, ← integral_add hDecay hGrow]
  apply integral_congr_ae
  filter_upwards with u
  have ha : -Complex.I * (-Complex.I / 2) * (u : ℂ) = ((-u / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hb : -Complex.I * (Complex.I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [ha, hb, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_nonpos hu]
    ring_nf

private theorem continuous_prime_main_eq_growing (f : WeilTestFunction) :
    (∫ u : ℝ in Ioi 0,
        (Real.exp (u / 2) : ℂ) *
          (convolutionSquare f u + convolutionSquare f (-u))) =
      ∫ u : ℝ, (Real.exp (|u| / 2) : ℂ) * convolutionSquare f u := by
  let h : ℝ -> ℂ := fun u =>
    (Real.exp (|u| / 2) : ℂ) * convolutionSquare f u
  have hIntegrable : Integrable h :=
    ((by fun_prop : Continuous fun u : ℝ => (Real.exp (|u| / 2) : ℂ)).mul
      (convolutionSquare f).continuous).integrable_of_hasCompactSupport
        (convolutionSquare f).hasCompactSupport.mul_left
  have hEven (u : ℝ) : h (-u) = h u := by
    simp only [h, abs_neg, convolutionSquare_even]
  have hLeftRight : (∫ u : ℝ in Iic 0, h u) = ∫ u : ℝ in Ioi 0, h u := by
    calc
      (∫ u : ℝ in Iic 0, h u) = ∫ u : ℝ in Iic 0, h (-u) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro u _hu
        exact (hEven u).symm
      _ = ∫ u : ℝ in Ioi 0, h u := by
        simpa only [neg_zero] using integral_comp_neg_Iic 0 h
  calc
    (∫ u : ℝ in Ioi 0,
        (Real.exp (u / 2) : ℂ) *
          (convolutionSquare f u + convolutionSquare f (-u))) =
        ∫ u : ℝ in Ioi 0, 2 * h u := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          dsimp only [h]
          rw [abs_of_pos hu, convolutionSquare_even]
          ring
    _ = 2 * ∫ u : ℝ in Ioi 0, h u := by rw [integral_const_mul]
    _ = (∫ u : ℝ in Iic 0, h u) + ∫ u : ℝ in Ioi 0, h u := by
          rw [hLeftRight]
          ring
    _ = ∫ u : ℝ, h u :=
      intervalIntegral.integral_Iic_add_Ioi hIntegrable.integrableOn
        hIntegrable.integrableOn

private theorem decaying_convolution_eq_green_kernel (f : WeilTestFunction) :
    (∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * convolutionSquare f u) =
      ∫ x : ℝ, ∫ y : ℝ,
        (Real.exp (-|x - y| / 2) : ℂ) * f x * conj (f y) := by
  let kernel : ℝ -> ℂ := fun u => (Real.exp (-|u| / 2) : ℂ)
  let integrand : ℝ × ℝ -> ℂ := fun p =>
    kernel p.1 * f p.2 * conj (f (p.2 - p.1))
  have hContinuous : Continuous integrand := by
    dsimp only [integrand, kernel]
    exact
      (((by fun_prop : Continuous fun p : ℝ × ℝ =>
          (Real.exp (-|p.1| / 2) : ℂ)).mul
        (f.continuous.comp continuous_snd)).mul
          (Complex.continuous_conj.comp
            (f.continuous.comp (continuous_snd.sub continuous_fst))))
  have hCompact : HasCompactSupport integrand := by
    refine HasCompactSupport.intro
      ((f.hasCompactSupport.isCompact.add f.hasCompactSupport.isCompact.neg).prod
        f.hasCompactSupport.isCompact) ?_
    rintro ⟨u, x⟩ hux
    rw [mem_prod, not_and_or] at hux
    rcases hux with hu | hx
    · by_cases hxf : x ∈ tsupport (f : ℝ -> ℂ)
      · have hxuf : x - u ∉ tsupport (f : ℝ -> ℂ) := by
          intro hxu
          exact hu ⟨x, hxf, -(x - u), by simpa using hxu, by ring⟩
        dsimp only [integrand]
        rw [image_eq_zero_of_notMem_tsupport hxuf, map_zero, mul_zero]
      · dsimp only [integrand]
        rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero, zero_mul]
    · dsimp only [integrand]
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, zero_mul]
  have hIntegrable : Integrable integrand (volume.prod volume) :=
    hContinuous.integrable_of_hasCompactSupport hCompact
  have hShift (x : ℝ) :
      (∫ u : ℝ, kernel u * f x * conj (f (x - u))) =
        ∫ y : ℝ, kernel (x - y) * f x * conj (f y) := by
    rw [← integral_sub_left_eq_self
      (fun u : ℝ => kernel u * f x * conj (f (x - u))) volume x]
    apply integral_congr_ae
    filter_upwards with y
    simp only [sub_sub_self]
  calc
    (∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * convolutionSquare f u) =
        ∫ u : ℝ, ∫ x : ℝ, kernel u * f x * conj (f (x - u)) := by
          apply integral_congr_ae
          filter_upwards with u
          rw [convolutionSquare_apply, ← integral_const_mul]
          simp only [kernel, mul_assoc]
    _ = ∫ x : ℝ, ∫ u : ℝ, kernel u * f x * conj (f (x - u)) := by
          exact integral_integral_swap hIntegrable
    _ = ∫ x : ℝ, ∫ y : ℝ, kernel (x - y) * f x * conj (f y) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hShift x
    _ = ∫ x : ℝ, ∫ y : ℝ,
        (Real.exp (-|x - y| / 2) : ℂ) * f x * conj (f y) := by rfl

/-- For an even compactly supported smooth test, subtracting the continuous prime
main density from the completed-zeta pole pair leaves the decaying full-line Green
kernel quadratic form. -/
theorem pole_continuum_completion (f : WeilTestFunction) :
    poleTerm (convolutionSquare f) -
        (∫ u : ℝ in Ioi 0,
          (Real.exp (u / 2) : ℂ) *
            (convolutionSquare f u + convolutionSquare f (-u))) =
      ∫ x : ℝ, ∫ y : ℝ,
        (Real.exp (-|x - y| / 2) : ℂ) * f x * conj (f y) := by
  rw [pole_term_eq_decaying_add_growing,
    continuous_prime_main_eq_growing, add_sub_cancel_right,
    decaying_convolution_eq_green_kernel]

#print axioms pole_continuum_completion

/-- Adding the pole-continuum Green multiplier to the completed-zeta Archimedean
term shifts the real part of the digamma argument from `1 / 4` to `5 / 4`. -/
theorem archimedean_shift_completion (xi : ℝ) :
    let bInf :=
      (Complex.digamma ((1 / 4 : ℂ) + Complex.I * (xi : ℂ) / 2)).re -
          Real.log Real.pi +
        1 / (xi ^ 2 + 1 / 4)
    bInf =
      (Complex.digamma ((5 / 4 : ℂ) + Complex.I * (xi : ℂ) / 2)).re -
        Real.log Real.pi := by
  dsimp only
  let z : ℂ := (1 / 4 : ℂ) + Complex.I * (xi : ℂ) / 2
  have hz : ∀ m : ℕ, z ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    dsimp only [z] at hre
    norm_num at hre
    have : (4 : ℝ) * (m : ℝ) = -1 := by linarith
    have hmnonneg : 0 <= (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hrec := Complex.digamma_apply_add_one z hz
  have hshift : z + 1 = (5 / 4 : ℂ) + Complex.I * (xi : ℂ) / 2 := by
    dsimp only [z]
    ring
  have hinv : (z⁻¹).re = 1 / (xi ^ 2 + 1 / 4) := by
    rw [Complex.inv_re, Complex.normSq_apply]
    dsimp only [z]
    norm_num
    field_simp
    ring
  rw [← hshift, hrec, Complex.add_re, hinv]
  ring

#print axioms archimedean_shift_completion

end

end D5.S3.Weil.ZetaGamma.PoleContinuumCompletion

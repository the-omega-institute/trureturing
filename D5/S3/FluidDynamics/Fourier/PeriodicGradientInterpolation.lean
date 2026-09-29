/- GID: D5/S3/FluidDynamics/Fourier/PeriodicGradientInterpolation
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/PeriodicGradientInterpolation
   mirror-E: none(waiver:universal-analytic-estimate)
   anchors: []
   utility: periodic physical-amplitude control of derivative fourth moments
   digest: Periodic integration by parts bounds a derivative fourth moment
     by physical amplitude and second-derivative energy. -/

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.FluidDynamics.Fourier.PeriodicGradientInterpolation

open MeasureTheory Set

/-- A periodic one-dimensional derivative has an `L⁴` bound using the physical
amplitude of its primitive and the `L²` energy of its second derivative. -/
theorem periodic_deriv_fourth_moment (a b M : ℝ) (hab : a ≤ b) (hM : 0 ≤ M)
    (f fp fpp : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (fp x) x)
    (hfp : ∀ x, HasDerivAt fp (fpp x) x)
    (hfpp : Continuous fpp)
    (hfperiod : f b = f a) (hfpperiod : fp b = fp a)
    (hbound : ∀ x ∈ Icc a b, |f x| ≤ M) :
    (∫ x in a..b, fp x ^ 4) ≤ 9 * M ^ 2 * ∫ x in a..b, fpp x ^ 2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hpc : Continuous fp := continuous_iff_continuousAt.mpr fun x => (hfp x).continuousAt
  have hppc : Continuous fpp := hfpp
  have hcube (x : ℝ) : HasDerivAt (fun y => fp y ^ 3)
      (3 * fp x ^ 2 * fpp x) x := by
    simpa only [Nat.reduceSub] using! (hfp x).fun_pow 3
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := f) (v := fun x => fp x ^ 3)
    (u' := fp) (v' := fun x => 3 * fp x ^ 2 * fpp x)
    (fun x _ => hf x) (fun x _ => hcube x)
    (hpc.continuousOn.intervalIntegrable)
    (((continuous_const.mul (hpc.pow 2)).mul hppc).continuousOn.intervalIntegrable)
  have hibp' : (∫ x in a..b, fp x ^ 4) =
      ∫ x in a..b, -(3 * f x * fp x ^ 2 * fpp x) := by
    have hend : f b * fp b ^ 3 - f a * fp a ^ 3 = 0 := by
      rw [hfperiod, hfpperiod]
      ring
    rw [hend, zero_sub] at hibp
    calc
      (∫ x in a..b, fp x ^ 4) = ∫ x in a..b, fp x * fp x ^ 3 := by
        congr 1
        funext x
        ring
      _ = -(∫ x in a..b, f x * (3 * fp x ^ 2 * fpp x)) := by
        linarith only [hibp]
      _ = ∫ x in a..b, -(3 * f x * fp x ^ 2 * fpp x) := by
        rw [← intervalIntegral.integral_neg]
        congr 1
        funext x
        ring
  have hnegC : Continuous (fun x : ℝ => -(3 * f x * fp x ^ 2 * fpp x)) := by
    fun_prop
  have hrhsC : Continuous (fun x : ℝ => (fp x ^ 4 + 9 * M ^ 2 * fpp x ^ 2) / 2) := by
    fun_prop
  have hpowC : Continuous (fun x : ℝ => fp x ^ 4) := by fun_prop
  have hsecondC : Continuous (fun x : ℝ => fpp x ^ 2) := by fun_prop
  have hmono : (∫ x in a..b, -(3 * f x * fp x ^ 2 * fpp x)) ≤
      ∫ x in a..b, (fp x ^ 4 + 9 * M ^ 2 * fpp x ^ 2) / 2 := by
    exact intervalIntegral.integral_mono_on hab
      hnegC.continuousOn.intervalIntegrable
      hrhsC.continuousOn.intervalIntegrable (fun x hx => by
        have hbnd := hbound x hx
        have hfsq : f x ^ 2 ≤ M ^ 2 := by
          have hp := mul_nonneg (sub_nonneg.mpr hbnd)
            (add_nonneg hM (abs_nonneg (f x)))
          nlinarith [sq_abs (f x)]
        have hnonneg : 0 ≤ (M ^ 2 - f x ^ 2) * fpp x ^ 2 :=
          mul_nonneg (sub_nonneg.mpr hfsq) (sq_nonneg _)
        nlinarith [sq_nonneg (fp x ^ 2 + 3 * f x * fpp x), hnonneg])
  rw [← hibp'] at hmono
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add hpowC.continuousOn.intervalIntegrable
      ((hsecondC.const_mul (9 * M ^ 2)).continuousOn.intervalIntegrable),
    intervalIntegral.integral_const_mul] at hmono
  linarith

#print axioms periodic_deriv_fourth_moment

/-- The two-dimensional periodic gradient fourth moment is bounded by the
physical amplitude and the pure second derivatives. The measure is the
unnormalized square; the normalized torus bridge is separate. -/
theorem periodic_vector_gradient_fourth_moment
    (a b M : ℝ) (hab : a ≤ b) (hM : 0 ≤ M)
    (μ : Measure ℝ) (hμ : μ = volume.restrict (Ioc a b))
    (u ux uy uxx uyy : Fin 2 → ℝ → ℝ → ℝ)
    (hux : ∀ i y x, HasDerivAt (fun z => u i z y) (ux i x y) x)
    (huxx : ∀ i y x, HasDerivAt (fun z => ux i z y) (uxx i x y) x)
    (huy : ∀ i x y, HasDerivAt (fun z => u i x z) (uy i x y) y)
    (huyy : ∀ i x y, HasDerivAt (fun z => uy i x z) (uyy i x y) y)
    (huxxC : ∀ i y, Continuous (fun x => uxx i x y))
    (huyyC : ∀ i x, Continuous (fun y => uyy i x y))
    (hperiodX : ∀ i y, u i b y = u i a y ∧ ux i b y = ux i a y)
    (hperiodY : ∀ i x, u i x b = u i x a ∧ uy i x b = uy i x a)
    (hbound : ∀ x y, x ∈ Icc a b → y ∈ Icc a b →
      u 0 x y ^ 2 + u 1 x y ^ 2 ≤ M ^ 2)
    (hix : ∀ i, Integrable (fun p : ℝ × ℝ => ux i p.1 p.2 ^ 4) (μ.prod μ))
    (hiy : ∀ i, Integrable (fun p : ℝ × ℝ => uy i p.1 p.2 ^ 4) (μ.prod μ))
    (hixx : ∀ i, Integrable (fun p : ℝ × ℝ => uxx i p.1 p.2 ^ 2) (μ.prod μ))
    (hiyy : ∀ i, Integrable (fun p : ℝ × ℝ => uyy i p.1 p.2 ^ 2) (μ.prod μ))
    (hgrad : Integrable (fun p : ℝ × ℝ =>
      (ux 0 p.1 p.2 ^ 2 + ux 1 p.1 p.2 ^ 2 +
        uy 0 p.1 p.2 ^ 2 + uy 1 p.1 p.2 ^ 2) ^ 2) (μ.prod μ)) :
    (∫ p : ℝ × ℝ,
      (ux 0 p.1 p.2 ^ 2 + ux 1 p.1 p.2 ^ 2 +
        uy 0 p.1 p.2 ^ 2 + uy 1 p.1 p.2 ^ 2) ^ 2 ∂μ.prod μ) ≤
      36 * M ^ 2 * (∫ p : ℝ × ℝ,
        uxx 0 p.1 p.2 ^ 2 + uxx 1 p.1 p.2 ^ 2 +
          uyy 0 p.1 p.2 ^ 2 + uyy 1 p.1 p.2 ^ 2 ∂μ.prod μ) := by
  haveI : SFinite μ := by rw [hμ]; infer_instance
  have hmem : ∀ᵐ x ∂μ, x ∈ Icc a b := by
    rw [hμ]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact Ioc_subset_Icc_self hx
  have hcomp (i : Fin 2) (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
      |u i x y| ≤ M := by
    have hb := hbound x y hx hy
    fin_cases i
    · change |u 0 x y| ≤ M
      apply (sq_le_sq₀ (abs_nonneg _) hM).mp
      nlinarith [sq_abs (u 0 x y), sq_nonneg (u 1 x y)]
    · change |u 1 x y| ≤ M
      apply (sq_le_sq₀ (abs_nonneg _) hM).mp
      nlinarith [sq_abs (u 1 x y), sq_nonneg (u 0 x y)]
  have hX (i : Fin 2) :
      (∫ p : ℝ × ℝ, ux i p.1 p.2 ^ 4 ∂μ.prod μ) ≤
        9 * M ^ 2 * (∫ p : ℝ × ℝ, uxx i p.1 p.2 ^ 2 ∂μ.prod μ) := by
    have hs (y : ℝ) (hy : y ∈ Icc a b) :
        (∫ x, ux i x y ^ 4 ∂μ) ≤ 9 * M ^ 2 * (∫ x, uxx i x y ^ 2 ∂μ) := by
      have h := periodic_deriv_fourth_moment a b M hab hM
        (fun x => u i x y) (fun x => ux i x y) (fun x => uxx i x y)
        (hux i y) (huxx i y) (huxxC i y)
        (hperiodX i y).1 (hperiodX i y).2 (fun x hx => hcomp i x y hx hy)
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab] at h
      simpa only [hμ] using h
    have hm : (∫ y, (∫ x, ux i x y ^ 4 ∂μ) ∂μ) ≤
        ∫ y, 9 * M ^ 2 * (∫ x, uxx i x y ^ 2 ∂μ) ∂μ := by
      apply MeasureTheory.integral_mono_ae (hix i).integral_prod_right
        ((hixx i).integral_prod_right.const_mul (9 * M ^ 2))
      filter_upwards [hmem] with y hy
      exact hs y hy
    calc
      (∫ p : ℝ × ℝ, ux i p.1 p.2 ^ 4 ∂μ.prod μ) =
          ∫ y, (∫ x, ux i x y ^ 4 ∂μ) ∂μ := by
        exact (MeasureTheory.integral_integral
          (f := fun x y => ux i x y ^ 4) (hix i)).symm.trans
          (MeasureTheory.integral_integral_swap
            (f := fun x y => ux i x y ^ 4) (hix i))
      _ ≤ ∫ y, 9 * M ^ 2 * (∫ x, uxx i x y ^ 2 ∂μ) ∂μ := hm
      _ = 9 * M ^ 2 * (∫ p : ℝ × ℝ, uxx i p.1 p.2 ^ 2 ∂μ.prod μ) := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact (MeasureTheory.integral_integral_swap
          (f := fun x y => uxx i x y ^ 2) (hixx i)).symm.trans
          (MeasureTheory.integral_integral
            (f := fun x y => uxx i x y ^ 2) (hixx i))
  have hY (i : Fin 2) :
      (∫ p : ℝ × ℝ, uy i p.1 p.2 ^ 4 ∂μ.prod μ) ≤
        9 * M ^ 2 * (∫ p : ℝ × ℝ, uyy i p.1 p.2 ^ 2 ∂μ.prod μ) := by
    have hs (x : ℝ) (hx : x ∈ Icc a b) :
        (∫ y, uy i x y ^ 4 ∂μ) ≤ 9 * M ^ 2 * (∫ y, uyy i x y ^ 2 ∂μ) := by
      have h := periodic_deriv_fourth_moment a b M hab hM
        (fun y => u i x y) (fun y => uy i x y) (fun y => uyy i x y)
        (huy i x) (huyy i x) (huyyC i x)
        (hperiodY i x).1 (hperiodY i x).2 (fun y hy => hcomp i x y hx hy)
      rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab] at h
      simpa only [hμ] using h
    have hm : (∫ x, (∫ y, uy i x y ^ 4 ∂μ) ∂μ) ≤
        ∫ x, 9 * M ^ 2 * (∫ y, uyy i x y ^ 2 ∂μ) ∂μ := by
      apply MeasureTheory.integral_mono_ae (hiy i).integral_prod_left
        ((hiyy i).integral_prod_left.const_mul (9 * M ^ 2))
      filter_upwards [hmem] with x hx
      exact hs x hx
    calc
      (∫ p : ℝ × ℝ, uy i p.1 p.2 ^ 4 ∂μ.prod μ) =
          ∫ x, (∫ y, uy i x y ^ 4 ∂μ) ∂μ := by
        exact (MeasureTheory.integral_integral
          (f := fun x y => uy i x y ^ 4) (hiy i)).symm
      _ ≤ ∫ x, 9 * M ^ 2 * (∫ y, uyy i x y ^ 2 ∂μ) ∂μ := hm
      _ = 9 * M ^ 2 * (∫ p : ℝ × ℝ, uyy i p.1 p.2 ^ 2 ∂μ.prod μ) := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact MeasureTheory.integral_integral
          (f := fun x y => uyy i x y ^ 2) (hiyy i)
  have hfour : Integrable (fun p : ℝ × ℝ =>
      ux 0 p.1 p.2 ^ 4 + ux 1 p.1 p.2 ^ 4 +
        uy 0 p.1 p.2 ^ 4 + uy 1 p.1 p.2 ^ 4) (μ.prod μ) :=
    (((hix 0).add (hix 1)).add (hiy 0)).add (hiy 1)
  have hsecond : Integrable (fun p : ℝ × ℝ =>
      uxx 0 p.1 p.2 ^ 2 + uxx 1 p.1 p.2 ^ 2 +
        uyy 0 p.1 p.2 ^ 2 + uyy 1 p.1 p.2 ^ 2) (μ.prod μ) :=
    (((hixx 0).add (hixx 1)).add (hiyy 0)).add (hiyy 1)
  have hpoint (p : ℝ × ℝ) :
      (ux 0 p.1 p.2 ^ 2 + ux 1 p.1 p.2 ^ 2 +
        uy 0 p.1 p.2 ^ 2 + uy 1 p.1 p.2 ^ 2) ^ 2 ≤
      4 * (ux 0 p.1 p.2 ^ 4 + ux 1 p.1 p.2 ^ 4 +
        uy 0 p.1 p.2 ^ 4 + uy 1 p.1 p.2 ^ 4) := by
    let A := ux 0 p.1 p.2 ^ 2
    let B := ux 1 p.1 p.2 ^ 2
    let C := uy 0 p.1 p.2 ^ 2
    let D := uy 1 p.1 p.2 ^ 2
    calc
      (A + B + C + D) ^ 2 ≤ 4 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
        nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A - D),
          sq_nonneg (B - C), sq_nonneg (B - D), sq_nonneg (C - D)]
      _ = _ := by dsimp [A, B, C, D]; ring
  have hsumfour :
      (∫ p : ℝ × ℝ,
        ux 0 p.1 p.2 ^ 4 + ux 1 p.1 p.2 ^ 4 +
          uy 0 p.1 p.2 ^ 4 + uy 1 p.1 p.2 ^ 4 ∂μ.prod μ) =
      (∫ p : ℝ × ℝ, ux 0 p.1 p.2 ^ 4 ∂μ.prod μ) +
      (∫ p : ℝ × ℝ, ux 1 p.1 p.2 ^ 4 ∂μ.prod μ) +
      (∫ p : ℝ × ℝ, uy 0 p.1 p.2 ^ 4 ∂μ.prod μ) +
      (∫ p : ℝ × ℝ, uy 1 p.1 p.2 ^ 4 ∂μ.prod μ) := by
    calc
      _ = (∫ p : ℝ × ℝ,
          ux 0 p.1 p.2 ^ 4 + ux 1 p.1 p.2 ^ 4 + uy 0 p.1 p.2 ^ 4 ∂μ.prod μ) +
          (∫ p : ℝ × ℝ, uy 1 p.1 p.2 ^ 4 ∂μ.prod μ) := by
            simpa only [Pi.add_apply] using MeasureTheory.integral_add
              (((hix 0).add (hix 1)).add (hiy 0)) (hiy 1)
      _ = ((∫ p : ℝ × ℝ, ux 0 p.1 p.2 ^ 4 + ux 1 p.1 p.2 ^ 4 ∂μ.prod μ) +
          (∫ p : ℝ × ℝ, uy 0 p.1 p.2 ^ 4 ∂μ.prod μ)) +
          (∫ p : ℝ × ℝ, uy 1 p.1 p.2 ^ 4 ∂μ.prod μ) := by
            congr 1
            simpa only [Pi.add_apply] using MeasureTheory.integral_add
              ((hix 0).add (hix 1)) (hiy 0)
      _ = _ := by
            congr 1
            congr 1
            simpa only [Pi.add_apply] using MeasureTheory.integral_add (hix 0) (hix 1)
  have hsumsecond :
      (∫ p : ℝ × ℝ,
        uxx 0 p.1 p.2 ^ 2 + uxx 1 p.1 p.2 ^ 2 +
          uyy 0 p.1 p.2 ^ 2 + uyy 1 p.1 p.2 ^ 2 ∂μ.prod μ) =
      (∫ p : ℝ × ℝ, uxx 0 p.1 p.2 ^ 2 ∂μ.prod μ) +
      (∫ p : ℝ × ℝ, uxx 1 p.1 p.2 ^ 2 ∂μ.prod μ) +
      (∫ p : ℝ × ℝ, uyy 0 p.1 p.2 ^ 2 ∂μ.prod μ) +
      (∫ p : ℝ × ℝ, uyy 1 p.1 p.2 ^ 2 ∂μ.prod μ) := by
    calc
      _ = (∫ p : ℝ × ℝ,
          uxx 0 p.1 p.2 ^ 2 + uxx 1 p.1 p.2 ^ 2 + uyy 0 p.1 p.2 ^ 2 ∂μ.prod μ) +
          (∫ p : ℝ × ℝ, uyy 1 p.1 p.2 ^ 2 ∂μ.prod μ) := by
            simpa only [Pi.add_apply] using MeasureTheory.integral_add
              (((hixx 0).add (hixx 1)).add (hiyy 0)) (hiyy 1)
      _ = ((∫ p : ℝ × ℝ, uxx 0 p.1 p.2 ^ 2 + uxx 1 p.1 p.2 ^ 2 ∂μ.prod μ) +
          (∫ p : ℝ × ℝ, uyy 0 p.1 p.2 ^ 2 ∂μ.prod μ)) +
          (∫ p : ℝ × ℝ, uyy 1 p.1 p.2 ^ 2 ∂μ.prod μ) := by
            congr 1
            simpa only [Pi.add_apply] using MeasureTheory.integral_add
              ((hixx 0).add (hixx 1)) (hiyy 0)
      _ = _ := by
            congr 1
            congr 1
            simpa only [Pi.add_apply] using MeasureTheory.integral_add (hixx 0) (hixx 1)
  have hbase := MeasureTheory.integral_mono hgrad (hfour.const_mul 4) hpoint
  rw [MeasureTheory.integral_const_mul, hsumfour] at hbase
  rw [hsumsecond]
  have hsum := add_le_add (add_le_add (add_le_add (hX 0) (hX 1)) (hY 0)) (hY 1)
  have hmul := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 4)
  nlinarith only [hbase, hmul]

#print axioms periodic_vector_gradient_fourth_moment

end D5.S3.FluidDynamics.Fourier.PeriodicGradientInterpolation

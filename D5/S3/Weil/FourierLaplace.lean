/- GID: D5/S3/Weil/FourierLaplace
   generality: I
   mirror-B: none(waiver:formal-analysis-foundation-only)
   mirror-E: none(waiver:structural-closure-properties-only)
   anchors: []
   digest: Define the complex Fourier-Laplace transform and prove its conjugation symmetries. -/

import D5.S3.Weil.TestFunctions
import Mathlib.MeasureTheory.Group.Integral

namespace D5.S3.Weil.FourierLaplace

open MeasureTheory
open D5.S3.Weil.Convention D5.S3.Weil.TestFunctions
open scoped ComplexConjugate

/-- The concrete angular-frequency Fourier-Laplace transform. -/
noncomputable def fourierLaplace (g : WeilTestFunction) (z : ℂ) : ℂ :=
  ∫ x : ℝ, fourierKernel z x * g x

theorem fourierLaplace_apply (g : WeilTestFunction) (z : ℂ) :
    fourierLaplace g z = ∫ x : ℝ, Complex.exp (-Complex.I * z * (x : ℂ)) * g x :=
  rfl

/-- Reflection of the angular kernel across complex conjugation. -/
theorem fourierKernel_neg_conj (z : ℂ) (x : ℝ) :
    fourierKernel z (-x) = conj (fourierKernel (conj z) x) := by
  simp only [fourierKernel]
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- The involution transforms into conjugation after reflecting the spectral parameter. -/
theorem fourierLaplace_involution_conj (g : WeilTestFunction) (z : ℂ) :
    fourierLaplace (involution g) z = conj (fourierLaplace g (conj z)) := by
  unfold fourierLaplace
  rw [← integral_conj]
  rw [← integral_neg_eq_self
    (fun x : ℝ => fourierKernel z x * involution g x) volume]
  apply integral_congr_ae
  filter_upwards with x
  rw [involution_apply]
  simp only [neg_neg, map_mul]
  rw [fourierKernel_neg_conj]

/-- On the real axis, the Weil involution becomes ordinary complex conjugation. -/
theorem fourierLaplace_involution_real (g : WeilTestFunction) (xi : ℝ) :
    fourierLaplace (involution g) xi = conj (fourierLaplace g xi) := by
  simpa using fourierLaplace_involution_conj g (xi : ℂ)

/-- A real-valued even test has a real Fourier-Laplace transform on the real axis. -/
theorem fourierLaplace_real_axis (g : WeilTestFunction)
    (hreal : ∀ x, conj (g x) = g x) (xi : ℝ) :
    conj (fourierLaplace g xi) = fourierLaplace g xi := by
  have hinvolution : involution g = g := by
    ext x
    rw [involution_apply, g.even]
    exact hreal x
  have h := fourierLaplace_involution_real g xi
  rw [hinvolution] at h
  exact h.symm

end D5.S3.Weil.FourierLaplace

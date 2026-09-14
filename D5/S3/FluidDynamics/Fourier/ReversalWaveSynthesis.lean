/- GID: D5/S3/FluidDynamics/Fourier/ReversalWaveSynthesis
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Fourier/ReversalWaveSynthesis
   mirror-E: none(waiver:exact-trigonometric-source-identification)
   anchors: []
   utility: none
   digest: The reversal witness coefficients synthesize the stated smooth divergence-free real cosine fields. -/

import D5.S3.FluidDynamics.Fourier.LowModeReversalWitness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Convert

/-!
# Physical fields of the exact Fourier witness

This source identifies the finite input synthesis with the literal real fields
in Proposition 5.2, proves joint smoothness, periodicity in both active spatial
coordinates, and vanishing ordinary divergence. The third component is zero
and every field is independent of the third spatial coordinate.

It does not silently identify the coefficient acceleration operator with a
Sobolev-domain Leray operator or construct a Navier--Stokes solution. The
coefficient-level separation remains the theorem of LowModeReversalWitness.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis

open D5.S3.FluidDynamics.Fourier.LowModeReversalWitness
open scoped BigOperators ContDiff

/-- The character exp(i*k.x), written in real sine/cosine coordinates. -/
def character (k : Mode) (x y : ℝ) : ℂ :=
  (Real.cos ((k.1 : ℝ) * x + (k.2 : ℝ) * y) : ℂ) +
    Complex.I * (Real.sin ((k.1 : ℝ) * x + (k.2 : ℝ) * y) : ℂ)

/-- Literal finite synthesis using the same four frequencies and coefficients. -/
def synthesis (alpha beta x y : ℝ) (c : Fin 3) : ℂ :=
  ∑ j : Fin 4, inputAmplitude alpha beta j c * character (frequency j) x y

/-- The actual smooth velocity field, independent of the third coordinate. -/
def realVelocity (alpha beta x y : ℝ) (c : Fin 3) : ℝ :=
  if c = 0 then beta * Real.cos (y - x)
  else if c = 1 then alpha * Real.cos x + beta * Real.cos (y - x)
  else 0

/-- The finite Fourier data is exactly the advertised real cosine field. -/
theorem synthesis_eq_realVelocity (alpha beta x y : ℝ) (c : Fin 3) :
    synthesis alpha beta x y c = (realVelocity alpha beta x y c : ℂ) := by
  simp only [synthesis, Fin.sum_univ_four]
  fin_cases c <;>
    apply Complex.ext <;>
    norm_num [synthesis, realVelocity, character, frequency, inputAmplitude,
      Fin.ext_iff, Complex.mul_re, Complex.mul_im,
      Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub] <;> ring

/-- Both active spatial coordinates are jointly smooth to every finite order. -/
theorem realVelocity_contDiff (alpha beta : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => realVelocity alpha beta p.1 p.2) := by
  apply contDiff_pi.mpr
  intro c
  fin_cases c <;> dsimp [realVelocity] <;> fun_prop

/-- The literal field has the correct 2*pi period in each active coordinate. -/
theorem realVelocity_periodic (alpha beta x y : ℝ) :
    realVelocity alpha beta (x + 2 * Real.pi) y = realVelocity alpha beta x y ∧
    realVelocity alpha beta x (y + 2 * Real.pi) = realVelocity alpha beta x y := by
  constructor <;> funext c <;> fin_cases c <;>
    simp [realVelocity, Real.cos_sub, Real.cos_add, Real.sin_add,
      Real.cos_two_pi, Real.sin_two_pi]

private theorem shifted_cosine_x (beta x y : ℝ) :
    HasDerivAt (fun s : ℝ => beta * Real.cos (y - s))
      (beta * Real.sin (y - x)) x := by
  have h := (((hasDerivAt_const x y).sub (hasDerivAt_id x)).cos).const_mul beta
  simpa using h

private theorem shifted_cosine_y (beta x y : ℝ) :
    HasDerivAt (fun s : ℝ => beta * Real.cos (s - x))
      (-beta * Real.sin (y - x)) y := by
  have h := (((hasDerivAt_id y).sub_const x).cos).const_mul beta
  simpa [mul_neg] using h

/-- Ordinary coordinate derivatives give zero divergence; no symbolic
'divergence-free' label is used as a premise. -/
theorem realVelocity_divergence (alpha beta x y : ℝ) :
    deriv (fun s => realVelocity alpha beta s y 0) x +
      deriv (fun s => realVelocity alpha beta x s 1) y = 0 := by
  have hx : HasDerivAt (fun s => realVelocity alpha beta s y 0)
      (beta * Real.sin (y - x)) x := by
    simpa [realVelocity, Fin.ext_iff] using shifted_cosine_x beta x y
  have hy : HasDerivAt (fun s => realVelocity alpha beta x s 1)
      (-beta * Real.sin (y - x)) y := by
    simpa [realVelocity, Fin.ext_iff] using shifted_cosine_y beta x y
  rw [hx.deriv, hy.deriv]
  ring

#print axioms character
#print axioms synthesis
#print axioms realVelocity
#print axioms synthesis_eq_realVelocity
#print axioms realVelocity_contDiff
#print axioms realVelocity_periodic
#print axioms realVelocity_divergence

end D5.S3.FluidDynamics.Fourier.ReversalWaveSynthesis

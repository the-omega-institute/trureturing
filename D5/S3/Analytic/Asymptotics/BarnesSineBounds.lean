/- GID: D5/S3/Analytic/Asymptotics/BarnesSineBounds
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/BarnesSineBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complex sine supplies exponential lower bounds on contour lines. -/

/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Bastiaan J Braams
SPDX-License-Identifier: Apache-2.0

Adapted source port from bjbraams/lean-DLMF at
560b9475f35bbc6e4f5296631298859825091f7f. The selected declarations retain
their mathematical statements; imports, namespace and local integrability
ownership are adapted for this repository. Source slices and consumers are
identified in Library/Asymptotics/braams2026barnesmittagport.md.
Retire each port when this repository's pinned Mathlib supplies an equivalent
declaration, replacing its consumers with direct Mathlib calls.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

open Complex Real

namespace D5.S3.Analytic.Asymptotics.BarnesSineBounds

/-- `‖sin (x + iy)‖² = sin² x + sinh² y`. -/
private theorem barnesRes_sq_norm_sin (x y : ℝ) :
    ‖Complex.sin (x + y * I)‖ ^ 2 = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  have h : Complex.sin (x + y * I) = ((Real.sin x * Real.cosh y : ℝ) : ℂ) +
      ((Real.cos x * Real.sinh y : ℝ) : ℂ) * I := by
    rw [Complex.sin_add_mul_I]; push_cast; rfl
  rw [h, norm_add_mul_I, Real.sq_sqrt (by positivity)]
  have := Real.cosh_sq y
  have := Real.sin_sq_add_cos_sq x
  nlinarith [this]

/-- `|sin x| cosh y ≤ ‖sin (x + iy)‖`. -/
private theorem barnesRes_abs_sinh_le_norm_sin (x y : ℝ) : |Real.sinh y| ≤ ‖Complex.sin (x + y * I)‖ := by
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs, barnesRes_sq_norm_sin]
  nlinarith [sq_nonneg (Real.sin x)]

private theorem barnesRes_abs_sin_mul_cosh_le_norm_sin (x y : ℝ) :
    |Real.sin x| * Real.cosh y ≤ ‖Complex.sin (x + y * I)‖ := by
  rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), mul_pow, sq_abs, barnesRes_sq_norm_sin,
    Real.cosh_sq]
  have h1 : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  nlinarith [sq_nonneg (Real.sinh y), sq_nonneg (Real.sin x)]

/-- `‖sin(π(x+iy))‖ ≥ (|sin πx|/2) e^{π|y|}`. -/
theorem barnesRes_sin_lower_line (x y : ℝ) :
    |Real.sin (π*x)|/2 * Real.exp (π*|y|) ≤ ‖Complex.sin (π*((x:ℂ) + y*I))‖ := by
  have hw : (π:ℂ)*((x:ℂ) + y*I) = ((π*x:ℝ):ℂ) + ((π*y:ℝ):ℂ)*I := by push_cast; ring
  rw [hw]
  refine le_trans ?_ (barnesRes_abs_sin_mul_cosh_le_norm_sin (π*x) (π*y))
  have hcosh : Real.exp (π*|y|)/2 ≤ Real.cosh (π*y) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq]
    have := Real.exp_pos (-(π*|y|)); linarith
  have := abs_nonneg (Real.sin (π*x))
  nlinarith

theorem barnesRes_sin_lower_far (x : ℝ) {y : ℝ} (hy : 1 ≤ |y|) :
    1/4 * Real.exp (π*|y|) ≤ ‖Complex.sin (π*((x:ℂ) + y*I))‖ := by
  have hw : (π:ℂ)*((x:ℂ) + y*I) = ((π*x:ℝ):ℂ) + ((π*y:ℝ):ℂ)*I := by push_cast; ring
  rw [hw]
  refine le_trans ?_ (barnesRes_abs_sinh_le_norm_sin (π*x) (π*y))
  rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos, Real.sinh_eq]
  have h4 := Real.add_one_le_exp (π*|y|)
  have h5 : Real.exp (-(π*|y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  nlinarith [Real.two_le_pi]

end D5.S3.Analytic.Asymptotics.BarnesSineBounds

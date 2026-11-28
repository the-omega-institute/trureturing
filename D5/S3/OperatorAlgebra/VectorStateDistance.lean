/- GID: D5/S3/OperatorAlgebra/VectorStateDistance
   generality: G
   mirror-B: none(waiver:covered-by-pure-gnsextension-sectors-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The norm bound for a difference of vector expectations follows by polarization along the sum and difference of the unit vectors. -/

import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
Omega original.

The norm bound for a difference of vector expectations follows by
polarization along the sum and difference of the unit vectors.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace Omega.OperatorAlgebra.VectorStateDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The difference of two unit-vector expectations on a bounded operator. -/
theorem norm_expectation_sub_le (v w : H) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (r : ℝ) (hr : inner ℂ v w = (r : ℂ)) (T : H →L[ℂ] H) :
    ‖inner ℂ v (T v) - inner ℂ w (T w)‖ ≤ (2 * Real.sqrt (1 - r ^ 2)) * ‖T‖ := by
  have hc (x y : H) : ‖inner ℂ x (T y)‖ ≤ ‖x‖ * ‖T‖ * ‖y‖ := by
    calc
      _ ≤ ‖x‖ * ‖T y‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖T‖ * ‖y‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm
  have h := norm_add_le (inner ℂ (v + w) (T (v - w))) (inner ℂ (v - w) (T (v + w)))
  have hid : inner ℂ (v + w) (T (v - w)) + inner ℂ (v - w) (T (v + w)) =
      2 * (inner ℂ v (T v) - inner ℂ w (T w)) := by
    simp only [map_add, map_sub, inner_add_left, inner_sub_left, inner_add_right, inner_sub_right]
    ring
  rw [hid, norm_mul, Complex.norm_ofNat] at h
  have hle : 2 * ‖inner ℂ v (T v) - inner ℂ w (T w)‖ ≤ 2 * (‖v + w‖ * ‖v - w‖ * ‖T‖) :=
    h.trans ((add_le_add (hc (v + w) (v - w)) (hc (v - w) (v + w))).trans_eq (by ring))
  have hp := norm_add_sq (𝕜 := ℂ) v w
  have hm := norm_sub_sq (𝕜 := ℂ) v w
  simp only [hv, hw, hr, RCLike.re_eq_complex_re, Complex.ofReal_re] at hp hm
  have hs : (‖v + w‖ * ‖v - w‖) ^ 2 = 4 * (1 - r ^ 2) := by
    rw [mul_pow, hp, hm]
    ring
  have hd : 0 ≤ 1 - r ^ 2 := by nlinarith only [hs, sq_nonneg (‖v + w‖ * ‖v - w‖)]
  have he : ‖v + w‖ * ‖v - w‖ = 2 * Real.sqrt (1 - r ^ 2) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [hs, mul_pow, Real.sq_sqrt hd]
    ring
  rw [he] at hle
  exact (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)).mp hle

end Omega.OperatorAlgebra.VectorStateDistance

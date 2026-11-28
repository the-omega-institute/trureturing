/- GID: D5/S3/Geometry/UnitQuaternions/SU2TangentGeometry
   generality: G
   mirror-B: none(waiver:covered-by-su2-tangent-lower-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First-order round geometry of imaginary quaternion curves. -/

import D5.S3.Geometry.UnitQuaternions.UnitQuaternionMetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! Omega original.

First-order round geometry of imaginary quaternion curves. -/

noncomputable section
open scoped Quaternion InnerProductSpace Topology
open Filter

namespace SimpleGraph.SU2Tangent

open Omega.Geometry.UnitQuaternion

abbrev U := unitary ℍ[ℝ]
abbrev Imaginary := {x : ℍ[ℝ] // x.re = 0}

theorem chord_eq (p q : U) :
    ‖(p : ℍ[ℝ]) - q‖ = 2 * Real.sin (roundDist p q / 2) := by
  have hi := real_inner_mem_Icc_of_norm_eq_one (norm_coe p) (norm_coe q)
  have hc : Real.cos (roundDist p q) = ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ :=
    Real.cos_arccos hi.1 hi.2
  have hn := norm_sub_sq_real (p : ℍ[ℝ]) (q : ℍ[ℝ])
  rw [norm_coe, norm_coe] at hn
  have hs := Real.cos_two_mul (roundDist p q / 2)
  rw [show 2 * (roundDist p q / 2) = roundDist p q by ring] at hs
  have ht := Real.sin_sq_add_cos_sq (roundDist p q / 2)
  have hlo : 0 ≤ roundDist p q := Real.arccos_nonneg _
  have hhi : roundDist p q ≤ Real.pi := Real.arccos_le_pi _
  have hpos : 0 ≤ Real.sin (roundDist p q / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  nlinarith [norm_nonneg ((p : ℍ[ℝ]) - q)]

theorem chord_le_round (p q : U) : ‖(p : ℍ[ℝ]) - q‖ ≤ roundDist p q := by
  rw [chord_eq]
  have hp : 0 ≤ roundDist p q / 2 := div_nonneg (Real.arccos_nonneg _) (by norm_num)
  linarith [Real.sin_le hp]

theorem round_eq_arcsin_chord (p q : U) :
    roundDist p q = 2 * Real.arcsin (‖(p : ℍ[ℝ]) - q‖ / 2) := by
  rw [chord_eq]
  have hlo : 0 ≤ roundDist p q := Real.arccos_nonneg _
  have hhi : roundDist p q ≤ Real.pi := Real.arccos_le_pi _
  have h : Real.arcsin (Real.sin (roundDist p q / 2)) = roundDist p q / 2 :=
    Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)
  rw [show 2 * Real.sin (roundDist p q / 2) / 2 =
    Real.sin (roundDist p q / 2) by ring, h]
  ring

/-- A smooth unit-quaternion curve with prescribed imaginary velocity at one. -/
def ambientCurve (X : ℍ[ℝ]) (t : ℝ) : ℍ[ℝ] :=
  Real.cos (t * ‖X‖) • (1 : ℍ[ℝ]) + (Real.sin (t * ‖X‖) / ‖X‖) • X

theorem ambientCurve_zero (X : ℍ[ℝ]) : ambientCurve X 0 = 1 := by
  simp [ambientCurve]

theorem ambientCurve_norm (X : ℍ[ℝ]) (hX : X.re = 0) (t : ℝ) :
    ‖ambientCurve X t‖ = 1 := by
  by_cases hn : X = 0
  · simp [ambientCurve, hn]
  have hr : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hi : ⟪(1 : ℍ[ℝ]), X⟫_ℝ = 0 := by simp [Quaternion.inner_def, hX]
  have hs := norm_add_sq_real (Real.cos (t * ‖X‖) • (1 : ℍ[ℝ]))
    ((Real.sin (t * ‖X‖) / ‖X‖) • X)
  simp only [norm_smul, Real.norm_eq_abs, norm_one, mul_one, real_inner_smul_left,
    real_inner_smul_right, hi, mul_zero, add_zero, sq_abs, mul_pow, div_pow] at hs
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hr)] at hs
  rw [Real.cos_sq_add_sin_sq] at hs
  dsimp [ambientCurve]
  nlinarith [norm_nonneg (Real.cos (t * ‖X‖) • (1 : ℍ[ℝ]) +
    (Real.sin (t * ‖X‖) / ‖X‖) • X)]

def curve (X : ℍ[ℝ]) (hX : X.re = 0) (t : ℝ) : U :=
  ofUnit (ambientCurve X t) (ambientCurve_norm X hX t)

@[simp] theorem coe_curve (X : ℍ[ℝ]) (hX : X.re = 0) (t : ℝ) :
    ((curve X hX t : U) : ℍ[ℝ]) = ambientCurve X t := rfl

@[simp] theorem curve_zero (X : ℍ[ℝ]) (hX : X.re = 0) : curve X hX 0 = 1 := by
  apply Subtype.ext
  exact ambientCurve_zero X

theorem ambientCurve_deriv (X : ℍ[ℝ]) : HasDerivAt (ambientCurve X) X 0 := by
  by_cases hn : X = 0
  · subst X
    convert (hasDerivAt_const (0 : ℝ) (1 : ℍ[ℝ])) using 1 <;>
      first | rfl | (funext t; simp [ambientCurve]) | simp [ambientCurve]
  have hr : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const ‖X‖).cos.smul_const (1 : ℍ[ℝ])).add
    ((((hasDerivAt_id (0 : ℝ)).mul_const ‖X‖).sin.div_const ‖X‖).smul_const X)
  convert h using 1 <;> first | rfl | (ext t; rfl) | simp [hr]


theorem curve_neg (X : ℍ[ℝ]) (hX : X.re = 0) (t : ℝ) :
    curve (-X) (by simp [hX]) t = (curve X hX t)⁻¹ := by
  apply Subtype.ext
  rw [← Unitary.star_eq_inv, Unitary.coe_star]
  change ambientCurve (-X) t = star (ambientCurve X t)
  have hx : star X = -X := by ext <;> simp [hX]
  simp [ambientCurve, hx]

/-- The rescaled ambient displacement tends to the prescribed tangent vector. -/
theorem curve_slope (X : ℍ[ℝ]) :
    Tendsto (fun t : ℝ => t⁻¹ • (ambientCurve X t - 1)) (𝓝[>] 0) (𝓝 X) := by
  simpa only [zero_add, ambientCurve_zero] using
    (ambientCurve_deriv X).tendsto_slope_zero_right


/-- Round distance has the same first-order norm as ambient displacement. -/
theorem round_slope {p q : ℝ → U} {A B : ℍ[ℝ]}
    (hp : HasDerivAt (fun t => (p t : ℍ[ℝ])) A 0)
    (hq : HasDerivAt (fun t => (q t : ℍ[ℝ])) B 0)
    (hzero : p 0 = q 0) :
    Tendsto (fun t : ℝ => roundDist (p t) (q t) / t) (𝓝[>] 0) (𝓝 ‖A - B‖) := by
  have hdiff := (hp.sub hq).tendsto_slope_zero_right
  have hd : Tendsto (fun t : ℝ => ‖(p t : ℍ[ℝ]) - q t‖ / t)
      (𝓝[>] 0) (𝓝 ‖A - B‖) := by
    have hh := hdiff.norm
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Pi.sub_apply, zero_add, hzero, sub_self, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos (show 0 < t from ht), div_eq_inv_mul]
  have hz : Tendsto (fun t => ‖(p t : ℍ[ℝ]) - q t‖ / 2) (𝓝[>] 0) (𝓝 0) := by
    have hh := ((hp.continuousAt.sub hq.continuousAt).norm.div_const 2).tendsto
    simpa [hzero] using hh.mono_left nhdsWithin_le_nhds
  have ha : HasDerivAt Real.arcsin 1 0 := by
    simpa using Real.hasDerivAt_arcsin (by norm_num : (0 : ℝ) ≠ -1)
      (by norm_num : (0 : ℝ) ≠ 1)
  let ratio := Function.update (fun x : ℝ => (Real.arcsin x - Real.arcsin 0) / (x - 0)) 0 1
  have hr : Tendsto ratio (𝓝 0) (𝓝 1) := by
    simpa [ratio] using ha.continuousAt_div.tendsto
  have h := (hr.comp hz).mul hd
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [round_eq_arcsin_chord]
  dsimp only [ratio, Function.comp_apply]
  by_cases hn : ‖(p t : ℍ[ℝ]) - q t‖ / 2 = 0
  · have hh : ‖(p t : ℍ[ℝ]) - q t‖ = 0 := by linarith
    simp [hh]
  · rw [Function.update_of_ne hn]
    simp only [Real.arcsin_zero, sub_zero]
    have hh : ‖(p t : ℍ[ℝ]) - q t‖ ≠ 0 := by
      intro he; apply hn; simp [he]
    field_simp [hh]

/-- A triangle made from tangent curves has the additive triangle defect as its limit. -/
theorem triangle_slope (X Y Z : ℍ[ℝ]) (hX : X.re = 0) (hY : Y.re = 0)
    (hZ : Z.re = 0) :
    Tendsto (fun t : ℝ => roundDist (curve X hX t * curve Y hY t) (curve Z hZ t) / t)
      (𝓝[>] 0) (𝓝 ‖X + Y - Z‖) := by
  have hp : HasDerivAt (fun t => ((curve X hX t * curve Y hY t : U) : ℍ[ℝ]))
      (X + Y) 0 := by
    have hh := (ambientCurve_deriv X).mul (ambientCurve_deriv Y)
    convert hh using 1 <;> first | rfl | (funext t; rfl) | simp [ambientCurve_zero]
  exact round_slope hp (ambientCurve_deriv Z) (by simp)

end SimpleGraph.SU2Tangent

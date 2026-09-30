/- GID: D5/S3/Geometry/HyperbolicInversion
   generality: G
   mirror-B: D5/B/S3/Geometry/HyperbolicInversion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Geometry.Euclidean.Inversion.Basic]
   utility: none
   digest: Boundary-centered inversion acts isometrically on hyperbolic upper half-space. -/

import D5.S3.Geometry.HyperbolicDilation
import Mathlib.Geometry.Euclidean.Inversion.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.HyperbolicInversion

open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicDilation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
private theorem ambient_ne_zero (p : UpperHalfSpace E) :
    (p.1 : Ambient E) ≠ 0 := by
  intro h
  have hh : height p = 0 := by
    simpa [height] using congrArg (fun x : Ambient E => x.snd) h
  exact (ne_of_gt p.2) hh

omit [InnerProductSpace ℝ E] in
private theorem radius_pos (p : UpperHalfSpace E) :
    0 < dist (p.1 : Ambient E) 0 :=
  dist_pos.mpr (ambient_ne_zero p)

/-- Euclidean inversion about the boundary origin, restricted to positive height. -/
noncomputable def invertedPoint (p : UpperHalfSpace E) : UpperHalfSpace E :=
  positiveDilation ((dist (p.1 : Ambient E) 0)⁻¹ ^ 2)
    (sq_pos_of_pos (inv_pos.mpr (radius_pos p))) p

private theorem invertedPoint_coe (p : UpperHalfSpace E) :
    ((invertedPoint p).1 : Ambient E) =
      EuclideanGeometry.inversion 0 1 p.1 := by
  simp [invertedPoint, positiveDilation, EuclideanGeometry.inversion]

private theorem invertedPoint_height (p : UpperHalfSpace E) :
    height (invertedPoint p) =
      (dist (p.1 : Ambient E) 0)⁻¹ ^ 2 * height p := by
  rfl

/-- Boundary-centered inversion preserves the normalized hyperbolic distance. -/
theorem hyperbolicDist_invertedPoint (p q : UpperHalfSpace E) :
    hyperbolicDist (invertedPoint p) (invertedPoint q) =
      hyperbolicDist p q := by
  let rp := dist (p.1 : Ambient E) 0
  let rq := dist (q.1 : Ambient E) 0
  have hrp : 0 < rp := radius_pos p
  have hrq : 0 < rq := radius_pos q
  have hroot :
      √((rp⁻¹ ^ 2 * height p) * (rq⁻¹ ^ 2 * height q)) =
        (rp * rq)⁻¹ * √(height p * height q) := by
    calc
      _ = √((rp⁻¹ * rq⁻¹) ^ 2 * (height p * height q)) := by congr 1; ring
      _ = √((rp⁻¹ * rq⁻¹) ^ 2) * √(height p * height q) :=
        Real.sqrt_mul (sq_nonneg _) _
      _ = (rp⁻¹ * rq⁻¹) * √(height p * height q) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos (inv_pos.mpr hrp) (inv_pos.mpr hrq))]
      _ = (rp * rq)⁻¹ * √(height p * height q) := by rw [mul_inv_rev, mul_comm rp⁻¹ rq⁻¹]
  have hdist :
      dist ((invertedPoint p).1 : Ambient E) (invertedPoint q).1 =
        (rp * rq)⁻¹ * dist (p.1 : Ambient E) q.1 := by
    rw [invertedPoint_coe, invertedPoint_coe,
      EuclideanGeometry.dist_inversion_inversion (ambient_ne_zero p) (ambient_ne_zero q)]
    simp [rp, rq]
  have hrootne : √(height p * height q) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos p.2 q.2)).ne'
  change 2 * Real.arsinh
      (dist ((invertedPoint p).1 : Ambient E) (invertedPoint q).1 /
        (2 * √(height (invertedPoint p) * height (invertedPoint q)))) =
    2 * Real.arsinh
      (dist (p.1 : Ambient E) q.1 / (2 * √(height p * height q)))
  rw [hdist, invertedPoint_height, invertedPoint_height, hroot]
  congr 1
  field_simp [hrp.ne', hrq.ne', hrootne]

/-- Inversion about the boundary origin is an involutive hyperbolic isometry. -/
noncomputable def inversion : HyperbolicSpace E ≃ᵢ HyperbolicSpace E where
  toFun p := ⟨invertedPoint p.coordinates⟩
  invFun p := ⟨invertedPoint p.coordinates⟩
  left_inv := by
    intro p
    cases p with
    | mk p =>
      change (⟨invertedPoint (invertedPoint p)⟩ : HyperbolicSpace E) = ⟨p⟩
      congr 1
      apply Subtype.ext
      rw [invertedPoint_coe, invertedPoint_coe]
      exact EuclideanGeometry.inversion_inversion 0 (by norm_num) p.1
  right_inv := by
    intro p
    cases p with
    | mk p =>
      change (⟨invertedPoint (invertedPoint p)⟩ : HyperbolicSpace E) = ⟨p⟩
      congr 1
      apply Subtype.ext
      rw [invertedPoint_coe, invertedPoint_coe]
      exact EuclideanGeometry.inversion_inversion 0 (by norm_num) p.1
  isometry_toFun := Isometry.of_dist_eq fun p q =>
    hyperbolicDist_invertedPoint p.coordinates q.coordinates

#print axioms hyperbolicDist_invertedPoint
#print axioms inversion

end D5.S3.Geometry.HyperbolicInversion

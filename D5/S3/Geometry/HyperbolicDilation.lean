/- GID: D5/S3/Geometry/HyperbolicDilation
   generality: G
   mirror-B: D5/B/S3/Geometry/HyperbolicDilation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.UpperHalfPlane.Metric]
   utility: none
   digest: Positive dilations act by isometries on hyperbolic upper half-space. -/

import D5.S3.Geometry.HyperbolicUpperHalfSpace
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.HyperbolicDilation

open D5.S3.Geometry.HyperbolicUpperHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Multiply both the horizontal coordinate and the height by a positive real. -/
def positiveDilation (a : ℝ) (ha : 0 < a) (p : UpperHalfSpace E) :
    UpperHalfSpace E :=
  ⟨a • p.1, by
    change 0 < a * height p
    exact mul_pos ha p.2⟩

/-- Positive scaling cancels between Euclidean separation and height normalization. -/
theorem hyperbolicDist_positiveDilation (a : ℝ) (ha : 0 < a)
    (p q : UpperHalfSpace E) :
    hyperbolicDist (positiveDilation a ha p) (positiveDilation a ha q) =
      hyperbolicDist p q := by
  have hroot : √((a * height p) * (a * height q)) =
      a * √(height p * height q) := by
    calc
      _ = √((a * a) * (height p * height q)) := by congr 1; ring
      _ = √(a * a) * √(height p * height q) :=
        Real.sqrt_mul (mul_self_nonneg a) _
      _ = a * √(height p * height q) := by rw [Real.sqrt_mul_self ha.le]
  have hrootne : √(height p * height q) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos p.2 q.2)).ne'
  change 2 * Real.arsinh
      (dist (a • p.1) (a • q.1) /
        (2 * √((a * height p) * (a * height q)))) =
    2 * Real.arsinh
      (dist p.1 q.1 / (2 * √(height p * height q)))
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ha, hroot]
  congr 1
  field_simp [ha.ne', hrootne]

/-- A positive dilation is an isometric equivalence, with inverse scale. -/
noncomputable def dilation (a : ℝ) (ha : 0 < a) :
    HyperbolicSpace E ≃ᵢ HyperbolicSpace E where
  toFun p := ⟨positiveDilation a ha p.coordinates⟩
  invFun p := ⟨positiveDilation a⁻¹ (inv_pos.mpr ha) p.coordinates⟩
  left_inv := by
    intro p
    cases p with
    | mk p =>
      change (⟨positiveDilation a⁻¹ (inv_pos.mpr ha)
        (positiveDilation a ha p)⟩ : HyperbolicSpace E) = ⟨p⟩
      congr 1
      apply Subtype.ext
      change a⁻¹ • (a • p.1) = p.1
      simp [smul_smul, ha.ne']
  right_inv := by
    intro p
    cases p with
    | mk p =>
      change (⟨positiveDilation a ha
        (positiveDilation a⁻¹ (inv_pos.mpr ha) p)⟩ : HyperbolicSpace E) = ⟨p⟩
      congr 1
      apply Subtype.ext
      change a • (a⁻¹ • p.1) = p.1
      simp [smul_smul, ha.ne']
  isometry_toFun := Isometry.of_dist_eq fun p q =>
    hyperbolicDist_positiveDilation a ha p.coordinates q.coordinates

#print axioms hyperbolicDist_positiveDilation
#print axioms dilation

end D5.S3.Geometry.HyperbolicDilation

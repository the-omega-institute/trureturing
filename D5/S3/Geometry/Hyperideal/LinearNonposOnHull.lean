/- GID: D5/S3/Geometry/Hyperideal/LinearNonposOnHull
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LinearNonposOnHull
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Hull]
   utility: none
   digest: A linear functional nonpositive on a set remains nonpositive on its convex hull. -/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic

noncomputable section
open Set
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.LinearNonposOnHull

abbrev V := Fin 4 → ℝ

/-- A linear support inequality on generators extends across their convex hull. -/
theorem linear_nonpos_on_hull (s : Set V) (L : V →ₗ[ℝ] ℝ)
    (h : ∀ x ∈ s, L x ≤ 0) : ∀ x ∈ convexHull ℝ s, L x ≤ 0 := by
  change convexHull ℝ s ⊆ {x | L x ≤ 0}
  apply convexHull_min (fun x hx => h x hx)
  intro x hx y hy a b ha hb hab
  change L (a • x + b • y) ≤ 0
  simp only [map_add, map_smul, smul_eq_mul]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
    (mul_nonpos_of_nonneg_of_nonpos hb hy)

#print axioms linear_nonpos_on_hull

end D5.S3.Geometry.Hyperideal.LinearNonposOnHull

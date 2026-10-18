/- GID: D5/S3/Geometry/Hyperideal/CentralSquareCommutativity
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/CentralSquareCommutativity
   mirror-E: none(waiver:group-theoretic-realization)
   anchors: []
   utility: none
   digest: A central element v⁻¹u² forces the generators u and v to commute. -/

import Mathlib.Algebra.Group.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.CentralSquareCommutativity

/-- If `v⁻¹ u²` is central, then the two generators commute. -/
theorem central_v_inv_sq_implies_commute
    {G : Type*} [Group G] (u v : G)
    (hcentral : ∀ g : G, (v⁻¹ * u ^ 2) * g = g * (v⁻¹ * u ^ 2)) :
    u * v = v * u := by
  have hcancel : (v⁻¹ * u) * u ^ 2 = (u * v⁻¹) * u ^ 2 := by
    calc
      (v⁻¹ * u) * u ^ 2 = (v⁻¹ * u ^ 2) * u := by
        simp [pow_two, mul_assoc]
      _ = u * (v⁻¹ * u ^ 2) := hcentral u
      _ = (u * v⁻¹) * u ^ 2 := by
        simp [pow_two, mul_assoc]
  have hv : v⁻¹ * u = u * v⁻¹ := mul_right_cancel hcancel
  calc
    u * v = (v * (v⁻¹ * u)) * v := by simp
    _ = (v * (u * v⁻¹)) * v := by rw [hv]
    _ = v * u := by simp [mul_assoc]

end D5.S3.Geometry.Hyperideal.CentralSquareCommutativity

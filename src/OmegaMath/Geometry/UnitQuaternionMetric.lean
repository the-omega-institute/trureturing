import OmegaBuild.Commands
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Quaternion
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

compile_only_with_mathlib

/-!
Omega original.

The round distance on unit quaternions is the angle in their real
inner product space. Both multiplication actions preserve this distance.
-/

open scoped InnerProductSpace Quaternion

noncomputable section

namespace Omega.Geometry.UnitQuaternion

local notation "U" => unitary ℍ[ℝ]

/-- The round geodesic distance on the unit quaternions. -/
def roundDist (p q : U) : ℝ := Real.arccos ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ

theorem norm_coe (p : U) : ‖(p : ℍ[ℝ])‖ = 1 :=
  CStarRing.norm_coe_unitary p

/-- A quaternion of norm one is unitary. -/
def ofUnit (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : U := by
  refine ⟨q, Unitary.mem_iff.mpr ?_⟩
  have h : ((Quaternion.normSq q : ℝ) : ℍ[ℝ]) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, hq, mul_one, Quaternion.coe_one]
  exact ⟨(Quaternion.star_mul_self q).trans h, (Quaternion.self_mul_star q).trans h⟩

@[simp] theorem coe_ofUnit (q : ℍ[ℝ]) (hq : ‖q‖ = 1) : ((ofUnit q hq : U) : ℍ[ℝ]) = q :=
  rfl

theorem round_eq_angle (p q : U) :
    roundDist p q = InnerProductGeometry.angle (p : ℍ[ℝ]) (q : ℍ[ℝ]) := by
  simp [roundDist, InnerProductGeometry.angle]

theorem round_nonneg (p q : U) : 0 ≤ roundDist p q :=
  Real.arccos_nonneg _

theorem round_le_pi (p q : U) : roundDist p q ≤ Real.pi :=
  Real.arccos_le_pi _

@[simp] theorem round_self (p : U) : roundDist p p = 0 := by
  simp [roundDist]

theorem round_comm (p q : U) : roundDist p q = roundDist q p := by
  rw [roundDist, roundDist, real_inner_comm]

theorem round_triangle (p q r : U) : roundDist p r ≤ roundDist p q + roundDist q r := by
  simpa only [round_eq_angle] using
    InnerProductGeometry.angle_le_angle_add_angle (p : ℍ[ℝ]) (q : ℍ[ℝ]) (r : ℍ[ℝ])

theorem round_mul_left (a p q : U) : roundDist (a * p) (a * q) = roundDist p q := by
  have h : ⟪(a : ℍ[ℝ]) * p, (a : ℍ[ℝ]) * q⟫_ℝ = ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ :=
    LinearIsometry.inner_map_map
      { toLinearMap := LinearMap.mulLeft ℝ (a : ℍ[ℝ])
        norm_map' := fun x => by simp [LinearMap.mulLeft_apply, norm_mul] } _ _
  exact congrArg Real.arccos h

theorem round_mul_right (a p q : U) : roundDist (p * a) (q * a) = roundDist p q := by
  have h : ⟪(p : ℍ[ℝ]) * a, (q : ℍ[ℝ]) * a⟫_ℝ = ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ :=
    LinearIsometry.inner_map_map
      { toLinearMap := LinearMap.mulRight ℝ (a : ℍ[ℝ])
        norm_map' := fun x => by simp [LinearMap.mulRight_apply, norm_mul] } _ _
  exact congrArg Real.arccos h

theorem round_inv (p q : U) : roundDist p⁻¹ q⁻¹ = roundDist p q := by
  calc
    _ = roundDist (p⁻¹ * p) (q⁻¹ * p) := (round_mul_right p _ _).symm
    _ = roundDist q p := by rw [inv_mul_cancel, ← round_mul_left q]; simp
    _ = _ := round_comm _ _

theorem round_edge (p g q : U) :
    roundDist g (p⁻¹ * q) = roundDist (p * g) q := by
  rw [← round_mul_left p g (p⁻¹ * q), mul_inv_cancel_left]

theorem round_le_iff (p q : U) {r : ℝ} (hr : 0 ≤ r) (hpi : r ≤ Real.pi) :
    roundDist p q ≤ r ↔ Real.cos r ≤ ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ := by
  have h := real_inner_mem_Icc_of_norm_eq_one (norm_coe p) (norm_coe q)
  have hc : Real.cos (roundDist p q) = ⟪(p : ℍ[ℝ]), (q : ℍ[ℝ])⟫_ℝ :=
    Real.cos_arccos h.1 h.2
  rw [← hc]
  exact (Real.strictAntiOn_cos.le_iff_ge ⟨hr, hpi⟩
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩).symm

end Omega.Geometry.UnitQuaternion

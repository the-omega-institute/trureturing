import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.GroupCliqueStrata
import OmegaMath.Combinatorics.Graph.ChordalWalkHolonomy

compile_only_with_mathlib

/-! Omega original.

Metric interpretations of normal defect sets and group residuals.
-/

namespace SimpleGraph.GroupCliqueMetricStrata
open scoped Pointwise
open GroupCliqueStrata (NormalSet)

variable {V H : Type*} [Group H] [PseudoMetricSpace H]
  [IsIsometricSMul H H] [IsIsometricSMul Hᵐᵒᵖ H]

theorem defectBall_normal {ε : ℝ} (hε : 0 ≤ ε) :
    NormalSet {x : H | Dist.dist x 1 ≤ ε} where
  one_mem := by simpa
  inv_mem := by
    intro x hx
    change Dist.dist x⁻¹ 1 ≤ ε
    simpa using (show Dist.dist x⁻¹ (1 : H)⁻¹ ≤ ε by rwa [dist_inv_inv])
  conj_mem := by
    intro a x hx
    change Dist.dist (a * x * a⁻¹) 1 ≤ ε
    simpa only [mul_one, mul_inv_cancel] using
      (show Dist.dist (a * x * a⁻¹) (a * 1 * a⁻¹) ≤ ε by rwa [dist_mul_right, dist_mul_left])

omit [IsIsometricSMul Hᵐᵒᵖ H] in
theorem defectBall_word_bound {ε : ℝ} {n : ℕ} {x : H}
    (hx : x ∈ ({y : H | Dist.dist y 1 ≤ ε} : Set H) ^ n) :
    Dist.dist x 1 ≤ (n : ℝ) * ε := by
  induction n generalizing x with
  | zero =>
    have he : x = 1 := by simpa using hx
    simp [he]
  | succ n ih =>
    rw [pow_succ, Set.mem_mul] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    have h₁ : Dist.dist (u * v) u = Dist.dist v 1 := by
      simpa using (dist_mul_left u v 1)
    have h₂ : Dist.dist v 1 ≤ ε := hv
    have h₃ := ih hu
    have ht := _root_.dist_triangle (u * v) u 1
    rw [h₁] at ht
    push_cast
    linarith

theorem residual_distance (g : V → V → H) (φ : V → H) (x y : V) :
    Dist.dist (GroupCliqueStrata.residual g φ x y) 1 = Dist.dist (g x y) ((φ x)⁻¹ * φ y) := by
  unfold GroupCliqueStrata.residual
  rw [show (1 : H) = (φ x * ((φ x)⁻¹ * φ y)) * (φ y)⁻¹ by group,
    dist_mul_right, dist_mul_left]

end SimpleGraph.GroupCliqueMetricStrata

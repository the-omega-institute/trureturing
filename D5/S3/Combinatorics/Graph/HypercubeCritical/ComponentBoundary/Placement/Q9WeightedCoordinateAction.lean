import D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized

/-! Coordinate actions transport the weighted signed cube operator, including
all independent coordinate weights. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9WeightedCoordinateAction

open scoped BigOperators
open Finset
open BalancedCriticalSpectrum (Q gamma gamma_apply)
local notation "flip" => BalancedCriticalSpectrum.flip
open Q9IsotropicHuang (weightedLinear parity)
open private weighted_sum from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SignedContactCells
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (normalize)
open private normalize_flip_axis mem_normalize_map parity_normalize_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoNormalized

/-- A single switching phase transports the whole coordinate-weighted family
through a cube isometry. Weights are permuted by the same action on axes. -/
theorem exists_weighted_coordinate_covariance (e : Q 9 ≃ Q 9) (p : Fin 9 ≃ Fin 9)
    (he : ∀ x i, e (flip x i) = flip (e x) (p i)) :
    ∃ θ : Q 9 → ℝ, (∀ x, θ x = 1 ∨ θ x = -1) ∧
      ∀ (w : Fin 9 → ℝ) (f : Q 9 → ℝ) (x : Q 9),
        weightedLinear w (fun y => θ (e.symm y) * f (e.symm y)) (e x) =
          θ x * weightedLinear (fun i => w (p i)) f x := by
  obtain ⟨θ, hθ, hedge, _⟩ := HuangCubeCovariance.exists_signed_covariance e p he
  refine ⟨θ, hθ, fun w f x => ?_⟩
  let F := fun y => θ (e.symm y) * f (e.symm y)
  change weightedLinear w F (e x) = _
  have hγ (i : Fin 9) : gamma (p i) F (e x) = θ x * gamma i f x := by
    rw [gamma_apply, gamma_apply, ← he, hedge]
    simp only [F, Equiv.symm_apply_apply]
    have hs : θ (flip x i) ^ 2 = 1 := by
      rcases hθ (flip x i) with h | h <;> rw [h] <;> norm_num
    calc
      _ = θ (flip x i) ^ 2 * (θ x * (huangMatrix 9 x (flip x i) * f (flip x i))) := by ring
      _ = _ := by rw [hs, one_mul]
  rw [weighted_sum, weighted_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Equiv.sum_comp p (fun i => w i * gamma i F (e x))]
  apply sum_congr rfl
  intro i _
  rw [hγ]
  ring

open Classical in
/-- Every parity-supported exterior solution transports along a normalized
frame with the corresponding relabeling of its independent weights. -/
theorem normalize_weighted_exterior_solution (S : Finset (Q 9)) (σ : Equiv.Perm (Fin 9))
    (o : Q 9) (b : Bool) (w : Fin 9 → ℝ) (f : Q 9 → ℝ)
    (hf : ∀ x, f x ≠ 0 ↔ x ∈ S ∧ parity x = b)
    (hzero : ∀ x ∉ S, weightedLinear (fun i => w (σ.symm i)) f x = 0) :
    let T := S.map (normalize σ o).toEmbedding
    ∃ g : Q 9 → ℝ,
      (∀ y, g y ≠ 0 ↔ y ∈ T ∧ parity y = b + parity o) ∧
      (∀ y ∉ T, weightedLinear w g y = 0) := by
  let e := normalize σ o
  let T := S.map e.toEmbedding
  have he (x : Q 9) (i : Fin 9) : e (flip x i) = flip (e x) (σ.symm i) := by
    simpa only [Equiv.apply_symm_apply] using normalize_flip_axis σ o x (σ.symm i)
  obtain ⟨θ, hθ, hcov⟩ := exists_weighted_coordinate_covariance e σ.symm he
  let g := fun y => θ (e.symm y) * f (e.symm y)
  refine ⟨g, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    have hne : θ x ≠ 0 := by rcases hθ x with h | h <;> simp [h]
    change θ (e.symm (e x)) * f (e.symm (e x)) ≠ 0 ↔ e x ∈ T ∧ parity (e x) = b + parity o
    rw [Equiv.symm_apply_apply, mul_ne_zero_iff, and_iff_right hne, hf,
      mem_normalize_map, parity_normalize_eq]
  · intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx : x ∉ S := fun hx => hy ((mem_normalize_map σ o S x).mpr hx)
    rw [show weightedLinear w g (e x) = θ x * weightedLinear (fun i => w (σ.symm i)) f x from hcov w f x,
      hzero x hx, mul_zero]

#print axioms exists_weighted_coordinate_covariance
#print axioms normalize_weighted_exterior_solution

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9WeightedCoordinateAction

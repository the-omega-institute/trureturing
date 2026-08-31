/- GID: D5/S3/Arith/Lattices/IcosahedralExteriorSquareHodgeSplitting
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The six-dimensional Hodge operator splits into complementary three-dimensional eigenspaces. -/

import D5.S3.Arith.Lattices.ExactDualLatticeFormula
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Module

/- Library-search audit trail (2026-09-01):
   * Repository searches for `exteriorPower`, `wedge`, `alternatingGroup`, `A5`, `icosahedral`,
     and eigenspace decompositions found no representation-theoretic exterior-square splitting.
     `ExactDualLatticeFormula` is the unique owner of the source's six-dimensional Hodge matrix.
   * Pinned Mathlib supplies `Module.End.eigenspace`, `Submodule.prodEquivOfIsCompl`, and
     `Submodule.finrank_add_eq_of_isCompl`, but no concrete real character table for `A5`, no
     exterior-power character formula, and no converse from character equality to an isomorphism.
   * Searches over every other pinned package found no finite-group representation result covering
     this calculation. The matrix identities and eigenspace dimensions are therefore proved here.
-/

namespace D5.S3.Arith.Lattices.IcosahedralExteriorSquareHodgeSplitting

open D5.S3.Arith.Lattices.ExactDualLatticeFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- The Hodge discriminant matrix as a real endomorphism of the six wedge coordinates. -/
def hodgeEnd : Module.End ℝ AmbientSpace :=
  Matrix.mulVecLin hodgeMatrix

/-- The positive square-root eigenspace of the Hodge discriminant operator. -/
def positiveEigenspace : Submodule ℝ AmbientSpace :=
  Module.End.eigenspace hodgeEnd √5

/-- The negative square-root eigenspace of the Hodge discriminant operator. -/
def negativeEigenspace : Submodule ℝ AmbientSpace :=
  Module.End.eigenspace hodgeEnd (-√5)

private lemma sqrt_five_pos : (0 : ℝ) < √5 := by
  positivity

private lemma sqrt_five_sq : (√5 : ℝ) ^ 2 = 5 := by
  norm_num

/-- The source matrix satisfies the quadratic relation `J² = 5I`. -/
theorem hodge_end_sq_apply (x : AmbientSpace) :
    hodgeEnd (hodgeEnd x) = (5 : ℝ) • x := by
  ext i
  fin_cases i <;>
    simp [hodgeEnd, hodgeMatrix, integralHodgeMatrix, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

private lemma hodge_eigenspaces_disjoint :
    Disjoint positiveEigenspace negativeEigenspace := by
  rw [disjoint_iff, Submodule.eq_bot_iff]
  intro x hx
  have hpos : hodgeEnd x = (√5 : ℝ) • x := by
    exact Module.End.mem_eigenspace_iff.mp hx.1
  have hneg : hodgeEnd x = (-√5 : ℝ) • x := by
    exact Module.End.mem_eigenspace_iff.mp hx.2
  have hzero : ((√5 : ℝ) - (-√5 : ℝ)) • x = 0 := by
    rw [sub_smul, ← hpos, ← hneg, sub_self]
  have hcoefficient : (√5 : ℝ) - (-√5 : ℝ) ≠ 0 := by
    nlinarith [sqrt_five_pos]
  exact (smul_eq_zero.mp hzero).resolve_left hcoefficient

private lemma hodge_eigenspaces_codisjoint :
    Codisjoint positiveEigenspace negativeEigenspace := by
  rw [Submodule.codisjoint_iff_exists_add_eq]
  intro x
  let c : ℝ := (2 * √5)⁻¹
  let p : AmbientSpace := c • ((√5 : ℝ) • x + hodgeEnd x)
  let m : AmbientSpace := c • ((√5 : ℝ) • x - hodgeEnd x)
  have hp : p ∈ positiveEigenspace := by
    rw [positiveEigenspace, Module.End.mem_eigenspace_iff]
    dsimp [p]
    rw [map_smul, map_add, map_smul, hodge_end_sq_apply]
    simp only [smul_add, smul_smul]
    match_scalars
    · ring
    · convert congrArg (fun z : ℝ => c * z) sqrt_five_sq.symm using 1 <;> ring
  have hm : m ∈ negativeEigenspace := by
    rw [negativeEigenspace, Module.End.mem_eigenspace_iff]
    dsimp [m]
    rw [map_smul, map_sub, map_smul, hodge_end_sq_apply]
    simp only [smul_sub, smul_smul]
    match_scalars
    · ring
    · convert congrArg (fun z : ℝ => -(c * z)) sqrt_five_sq.symm using 1 <;> ring
  refine ⟨p, m, hp, hm, ?_⟩
  dsimp [p, m, c]
  simp only [smul_add, smul_sub]
  match_scalars
  · field_simp [sqrt_five_pos.ne'] <;> norm_num
  · ring

/-- The two real Hodge eigenspaces are complementary. -/
theorem hodge_eigenspaces_isCompl :
    IsCompl positiveEigenspace negativeEigenspace :=
  ⟨hodge_eigenspaces_disjoint, hodge_eigenspaces_codisjoint⟩

/-- Reversing the orientation of the underlying four-dimensional coordinates on wedge pairs. -/
def orientationReverse : Module.End ℝ AmbientSpace where
  toFun x := ![-x 0, x 3, x 4, x 1, x 2, x 5]
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' a x := by ext i; fin_cases i <;> simp

private lemma orientation_reverse_involutive : Function.Involutive orientationReverse := by
  intro x
  ext i
  fin_cases i <;> simp [orientationReverse]

private lemma orientation_reverse_anticommutes (x : AmbientSpace) :
    hodgeEnd (orientationReverse x) = -orientationReverse (hodgeEnd x) := by
  ext i
  fin_cases i <;>
    simp [hodgeEnd, orientationReverse, hodgeMatrix, integralHodgeMatrix,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

private def positiveToNegative : positiveEigenspace →ₗ[ℝ] negativeEigenspace where
  toFun x := ⟨orientationReverse x, by
    rw [negativeEigenspace, Module.End.mem_eigenspace_iff]
    rw [orientation_reverse_anticommutes]
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    rw [hx, map_smul]
    simp⟩
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

private def negativeToPositive : negativeEigenspace →ₗ[ℝ] positiveEigenspace where
  toFun x := ⟨orientationReverse x, by
    rw [positiveEigenspace, Module.End.mem_eigenspace_iff]
    rw [orientation_reverse_anticommutes]
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    rw [hx, map_smul]
    simp⟩
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

/-- Orientation reversal exchanges the two Hodge eigenspaces. -/
def eigenspaceEquiv : positiveEigenspace ≃ₗ[ℝ] negativeEigenspace where
  toLinearMap := positiveToNegative
  invFun := negativeToPositive
  left_inv x := by
    ext i
    exact congrFun (orientation_reverse_involutive x) i
  right_inv x := by
    ext i
    exact congrFun (orientation_reverse_involutive x) i

private lemma eigenspace_finranks :
    Module.finrank ℝ positiveEigenspace = 3 ∧
      Module.finrank ℝ negativeEigenspace = 3 := by
  have hsum := Submodule.finrank_add_eq_of_isCompl hodge_eigenspaces_isCompl
  have htotal : Module.finrank ℝ AmbientSpace = 6 := by
    simp [AmbientSpace]
  have heq : Module.finrank ℝ positiveEigenspace =
      Module.finrank ℝ negativeEigenspace :=
    LinearEquiv.finrank_eq eigenspaceEquiv
  omega

/-- The six wedge coordinates split canonically into two complementary three-dimensional real
Hodge eigenspaces, with eigenvalues `√5` and `-√5`. -/
theorem icosahedral_exterior_square_hodge_splitting :
    Nonempty ((positiveEigenspace × negativeEigenspace) ≃ₗ[ℝ] AmbientSpace) ∧
      Module.finrank ℝ positiveEigenspace = 3 ∧
      Module.finrank ℝ negativeEigenspace = 3 := by
  exact ⟨⟨Submodule.prodEquivOfIsCompl positiveEigenspace negativeEigenspace
    hodge_eigenspaces_isCompl⟩, eigenspace_finranks⟩

#print axioms hodge_end_sq_apply
#print axioms hodge_eigenspaces_isCompl
#print axioms eigenspaceEquiv
#print axioms icosahedral_exterior_square_hodge_splitting

end

end D5.S3.Arith.Lattices.IcosahedralExteriorSquareHodgeSplitting

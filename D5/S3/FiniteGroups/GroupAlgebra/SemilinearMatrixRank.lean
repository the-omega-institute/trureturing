/- GID: D5/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/SemilinearMatrixRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Covariant Galois operators force multiplicity over the original division ring. -/

module

public import D5.S3.Factorization.Galois.TraceDualSkewMatrix
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Semilinear rank over the original division ring

The matrix-corner coordinates adapt `toModuleCatFromModuleCatLinearEquiv` in
Mathlib/RingTheory/Morita/Matrix.lean, by Yunzhou Xie and Jujian Zhang,
released under Apache 2.0. The independent scalar ring D is retained: linearity
comes from the target End D U, without a C-module or scalar tower on U.

The live client lifts actual covariant coefficient and Galois operators, then
pulls them back along the inverse trace-dual ordinary matrix equivalence.
This is the original-D rank input to Frobenius representation theory; no
Schur-index cancellation or full Frobenius theorem is asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.FiniteGroups.GroupAlgebra.SemilinearMatrixRank

open D5.S3.Factorization.Galois

namespace Corner

universe uD uC uI uU

variable {D : Type uD} {C : Type uC} {I : Type uI} {U : Type uU}
variable [DivisionRing D] [Ring C] [Fintype I] [DecidableEq I]
variable [AddCommGroup U] [Module D U]

section ExplicitCorner

variable (theta : Matrix I I C →+* Module.End D U) (i0 : I)

/-- The range of the chosen matrix idempotent, over the original D. -/
def corner : Submodule D U :=
  LinearMap.range (theta (Matrix.single i0 i0 1))

/-- Coordinates in the chosen corner. -/
def toCorner : U →ₗ[D] (I → corner theta i0) where
  toFun x i := ⟨theta (Matrix.single i0 i 1) x, by
    apply LinearMap.mem_range.mpr
    exact ⟨theta (Matrix.single i0 i 1) x, by
      rw [← Module.End.mul_apply, ← map_mul,
        Matrix.single_mul_single_same, one_mul]⟩⟩
  map_add' x y := by
    funext i
    apply Subtype.ext
    exact (theta (Matrix.single i0 i 1)).map_add x y
  map_smul' d x := by
    funext i
    apply Subtype.ext
    exact (theta (Matrix.single i0 i 1)).map_smul d x

/-- Reconstruction from corner coordinates, also D-linear. -/
def fromCorner : (I → corner theta i0) →ₗ[D] U where
  toFun s := ∑ i, theta (Matrix.single i i0 1) (s i : U)
  map_add' s t := by
    change (∑ i, theta (Matrix.single i i0 1) ((s i : U) + (t i : U))) =
      (∑ i, theta (Matrix.single i i0 1) (s i : U)) +
        ∑ i, theta (Matrix.single i i0 1) (t i : U)
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' d s := by
    change (∑ i, theta (Matrix.single i i0 1) (d • (s i : U))) =
      d • (∑ i, theta (Matrix.single i i0 1) (s i : U))
    simp only [LinearMap.map_smul, Finset.smul_sum]

/-- The matrix-corner equivalence, with multiplication in End interpreted as composition. -/
def cornerEquiv : U ≃ₗ[D] (I → corner theta i0) where
  toLinearMap := toCorner theta i0
  invFun := fromCorner theta i0
  left_inv x := by
    change (∑ i, theta (Matrix.single i i0 1)
      (theta (Matrix.single i0 i 1) x)) = x
    simp_rw [← Module.End.mul_apply, ← map_mul,
      Matrix.single_mul_single_same, one_mul]
    rw [← LinearMap.sum_apply, ← map_sum, Matrix.sum_single_one,
      map_one, Module.End.one_apply]
  right_inv s := by
    funext i
    apply Subtype.ext
    change theta (Matrix.single i0 i 1)
      (∑ j, theta (Matrix.single j i0 1) (s j : U)) = (s i : U)
    rw [map_sum]
    have hz (j : I) (hji : j ≠ i) :
        theta (Matrix.single i0 i 1)
          (theta (Matrix.single j i0 1) (s j : U)) = 0 := by
      rw [← Module.End.mul_apply, ← map_mul,
        Matrix.single_mul_single_of_ne (c := (1 : C)) i0 i j hji.symm (1 : C),
        map_zero, LinearMap.zero_apply]
    rw [Finset.sum_eq_single i (fun j _ hji => hz j hji) (by simp)]
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (s i).property
    rw [← Module.End.mul_apply, ← map_mul,
      Matrix.single_mul_single_same, one_mul]
    rw [← hx, ← Module.End.mul_apply, ← map_mul,
      Matrix.single_mul_single_same, one_mul]

/-- The exact rank identity for any chosen corner, including U = 0. -/
theorem finrank_eq_card_mul_corner [FiniteDimensional D U] :
    Module.finrank D U = Fintype.card I * Module.finrank D (corner theta i0) := by
  calc
    Module.finrank D U = Module.finrank D (I → corner theta i0) :=
      (cornerEquiv theta i0).finrank_eq
    _ = ∑ _ : I, Module.finrank D (corner theta i0) :=
      Module.finrank_pi_fintype D
    _ = Fintype.card I * Module.finrank D (corner theta i0) := by simp

end ExplicitCorner

variable (theta : Matrix I I C →+* Module.End D U)

include theta

/-- A unital matrix-ring action forces divisibility of the original D-rank. -/
theorem card_dvd_finrank [Nonempty I] [FiniteDimensional D U] :
    Fintype.card I ∣ Module.finrank D U := by
  let i0 : I := Classical.choice (inferInstance : Nonempty I)
  exact ⟨Module.finrank D (corner theta i0), finrank_eq_card_mul_corner theta i0⟩

/-- For nonzero U the original D-rank has positive multiplicity. -/
theorem exists_pos_rank [Nonempty I] [FiniteDimensional D U] [Nontrivial U] :
    ∃ r : ℕ, 0 < r ∧ Module.finrank D U = Fintype.card I * r := by
  obtain ⟨r, hr⟩ := card_dvd_finrank theta
  have hr0 : r ≠ 0 := by
    intro h0
    have hpos := Module.finrank_pos (R := D) (M := U)
    rw [hr, h0, mul_zero] at hpos
    exact (Nat.lt_irrefl 0) hpos
  exact ⟨r, Nat.pos_of_ne_zero hr0, hr⟩

end Corner

namespace Semilinear

universe uk uF uA uD uU uI

variable (k : Type uk) (F : Type uF) [Field k] [Field F] [Algebra k F]
  [FiniteDimensional k F] [IsGalois k F]
variable (A : Type uA) [Ring A] [Algebra F A]
  [Algebra k A] [IsScalarTower k F A]
  [MulSemiringAction (F ≃ₐ[k] F) A] [SMulDistribClass (F ≃ₐ[k] F) F A]
variable {D : Type uD} {U : Type uU} [DivisionRing D]
  [AddCommGroup U] [Module D U]

local notation "Γ" => F ≃ₐ[k] F

/-- The skew representation built from the supplied coefficient and group operators. -/
def skewRepresentation (a : A →+* Module.End D U) (tau : Γ →* Module.End D U)
    (covariance : ∀ (g : Γ) (x : A), tau g * a x = a (g • x) * tau g) :
    SkewMonoidAlgebra A Γ →+* Module.End D U :=
  SkewMonoidAlgebra.liftNCRingHom a tau (fun {x g} => (covariance g x).symm)

/-- Pull back the actual skew representation along the inverse ordinary matrix map. -/
def matrixAction (a : A →+* Module.End D U) (tau : Γ →* Module.End D U)
    (covariance : ∀ (g : Γ) (x : A), tau g * a x = a (g • x) * tau g)
    {I : Type uI} [Fintype I] [DecidableEq I]
    (b : Module.Basis I k F) :
    Matrix I I (TraceDualSkewMatrix.invariants k F A) →+* Module.End D U :=
  (skewRepresentation k F A a tau covariance).comp
    (TraceDualSkewMatrix.skewMatrixEquiv k F A b).symm.toRingEquiv.toRingHom

variable (a : A →+* Module.End D U) (tau : Γ →* Module.End D U)
  (covariance : ∀ (g : Γ) (x : A), tau g * a x = a (g • x) * tau g)

include a tau covariance in
/-- Galois symmetry divides the rank over the original, possibly noncommutative D. -/
theorem card_galois_dvd_finrank [FiniteDimensional D U] :
    Nat.card Γ ∣ Module.finrank D U := by
  letI : Nonempty (Fin (Module.finrank k F)) :=
    ⟨⟨0, Module.finrank_pos (R := k) (M := F)⟩⟩
  rw [IsGalois.card_aut_eq_finrank k F]
  simpa only [Fintype.card_fin] using
    Corner.card_dvd_finrank (matrixAction k F A a tau covariance (Module.finBasis k F))

include a tau covariance in
/-- A nonzero covariant module has a positive integral original-D multiplicity. -/
theorem exists_pos_galois_rank [FiniteDimensional D U] [Nontrivial U] :
    ∃ r : ℕ, 0 < r ∧ Module.finrank D U = Nat.card Γ * r := by
  letI : Nonempty (Fin (Module.finrank k F)) :=
    ⟨⟨0, Module.finrank_pos (R := k) (M := F)⟩⟩
  rw [IsGalois.card_aut_eq_finrank k F]
  simpa only [Fintype.card_fin] using
    Corner.exists_pos_rank (matrixAction k F A a tau covariance (Module.finBasis k F))

end Semilinear

end D5.S3.FiniteGroups.GroupAlgebra.SemilinearMatrixRank

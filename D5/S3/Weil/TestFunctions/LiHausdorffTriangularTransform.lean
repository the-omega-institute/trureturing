/- GID: D5/S3/Weil/TestFunctions/LiHausdorffTriangularTransform
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/LiHausdorffTriangularTransform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Li coefficients form an invertible triangular transform of trace moments. -/

import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-31):
   * D5 name and body-shape searches for a Li--Hausdorff transform, its
     binomial coefficient matrix, and an equivalent triangular map found no
     existing owner. Related Li and Laguerre modules state different analytic
     identities.
   * Pinned Mathlib has no exact Li coefficient transform. Its
     `Matrix.det_of_lowerTriangular`, `Matrix.mulVec_injective_iff_isUnit`, and
     `Matrix.mulVec_surjective_iff_isUnit` are applied directly below.
   * Installed non-Mathlib Lake packages contain no exact hit. Dependency-mode
     ecosystem admission remains wait-for-capability under specification A17. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Matrix

namespace D5.S3.Weil.TestFunctions.LiHausdorffTriangularTransform

/-- The finite-prefix coefficient matrix of the one-indexed Li--Hausdorff
transform. A matrix index `i` represents the source index `i + 1`. -/
def liHausdorffMatrix (N : Nat) : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  if j <= i then
    ((i.1 + 1 : Nat) : ℝ) *
      ((-1 : ℝ) ^ (j.1 + 2) * 4 ^ (j.1 + 1) / ((j.1 + 1 : Nat) : ℝ) *
        Nat.choose (i.1 + j.1 + 1) (i.1 - j.1))
  else
    0

/-- The coefficient matrix is lower triangular and invertible at every finite
depth; its action is the displayed Li coefficient sum, and the canonical
three-dimensional transform has the first three displayed inverse formulas. -/
theorem li_hausdorff_triangular_transform :
    (∀ N : Nat,
      (liHausdorffMatrix N).BlockTriangular
        (OrderDual.toDual : Fin N → OrderDual (Fin N))) ∧
    (∀ N : Nat, Function.Bijective (liHausdorffMatrix N).mulVec) ∧
    (∀ (N : Nat) (p : Fin N → ℝ) (i : Fin N),
      (liHausdorffMatrix N).mulVec p i =
        ((i.1 + 1 : Nat) : ℝ) *
          ∑ j ∈ Finset.Iic i,
            ((-1 : ℝ) ^ (j.1 + 2) * 4 ^ (j.1 + 1) /
              ((j.1 + 1 : Nat) : ℝ) *
              Nat.choose (i.1 + j.1 + 1) (i.1 - j.1)) * p j) ∧
    (∀ p : Fin 3 → ℝ,
      let lambda := (liHausdorffMatrix 3).mulVec p
      p 0 = lambda 0 / 4 ∧
      p 1 = (4 * lambda 0 - lambda 1) / 16 ∧
      p 2 = (lambda 2 + 15 * lambda 0 - 6 * lambda 1) / 64) := by
  constructor
  · intro N i j hji
    have hij : i < j := by simpa using hji
    simp [liHausdorffMatrix, not_le_of_gt hij]
  constructor
  · intro N
    have hlower :
        (liHausdorffMatrix N).BlockTriangular
          (OrderDual.toDual : Fin N → OrderDual (Fin N)) := by
      intro i j hji
      have hij : i < j := by simpa using hji
      simp [liHausdorffMatrix, not_le_of_gt hij]
    have hdiag (i : Fin N) : liHausdorffMatrix N i i ≠ 0 := by
      rw [liHausdorffMatrix, if_pos le_rfl]
      simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
      positivity
    have hdet : (liHausdorffMatrix N).det ≠ 0 := by
      rw [Matrix.det_of_lowerTriangular (liHausdorffMatrix N) hlower]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i
    have hunit : IsUnit (liHausdorffMatrix N).det :=
      isUnit_iff_ne_zero.mpr hdet
    have hmatrixUnit : IsUnit (liHausdorffMatrix N) :=
      (liHausdorffMatrix N).isUnit_iff_isUnit_det.mpr hunit
    exact
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hmatrixUnit,
        Matrix.mulVec_surjective_iff_isUnit.mpr hmatrixUnit⟩
  constructor
  · intro N p i
    rw [← Finset.filter_ge_eq_Iic]
    simp [liHausdorffMatrix, Matrix.mulVec, dotProduct, Finset.sum_ite,
      Finset.mul_sum, mul_assoc]
  · intro p
    dsimp
    norm_num [liHausdorffMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      show ¬(2 : Fin 3) ≤ 1 by decide, show (1 : Fin 3) ≤ 2 by decide]
    all_goals ring_nf
    all_goals simp

#print axioms li_hausdorff_triangular_transform

end D5.S3.Weil.TestFunctions.LiHausdorffTriangularTransform

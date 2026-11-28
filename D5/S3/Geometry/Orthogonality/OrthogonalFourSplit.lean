/- GID: D5/S3/Geometry/Orthogonality/OrthogonalFourSplit
   generality: G
   mirror-B: none(waiver:covered-by-dirac-hydrogen-fine-structure4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two cross-product factors of the definite four-dimensional orthogonal Lie algebra. -/

import OmegaBuild.Commands
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Prod
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Omega original.

The two cross-product factors of the definite four-dimensional orthogonal Lie algebra. -/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix

namespace OmegaMath.OrthogonalFourSplit

abbrev VectorThree := Fin 3 → ℝ
abbrev SoFour := LieAlgebra.Orthogonal.so (Fin 4) ℝ

attribute [local instance] Cross.lieRing

local instance : LieAlgebra ℝ VectorThree where
  lie_smul c x y := (crossProduct x).map_smul c y

private def splitCoordinates (X : Matrix (Fin 4) (Fin 4) ℝ) : VectorThree × VectorThree :=
  (![-X 1 2 + X 0 3, X 0 2 + X 1 3, -X 0 1 + X 2 3],
   ![-X 1 2 - X 0 3, X 0 2 - X 1 3, -X 0 1 - X 2 3])

private def joinCoordinates (v : VectorThree × VectorThree) : Matrix (Fin 4) (Fin 4) ℝ :=
  let p := v.1
  let q := v.2
  !![0, -(p 2 + q 2) / 2, (p 1 + q 1) / 2, (p 0 - q 0) / 2;
     (p 2 + q 2) / 2, 0, -(p 0 + q 0) / 2, (p 1 - q 1) / 2;
     -(p 1 + q 1) / 2, (p 0 + q 0) / 2, 0, (p 2 - q 2) / 2;
     -(p 0 - q 0) / 2, -(p 1 - q 1) / 2, -(p 2 - q 2) / 2, 0]

private def join (v : VectorThree × VectorThree) : SoFour := ⟨joinCoordinates v, by
  apply (LieAlgebra.Orthogonal.mem_so _ _ _).2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [joinCoordinates] <;> ring⟩

private theorem skew_entry (X : SoFour) (i j : Fin 4) :
    (X.1 : Matrix (Fin 4) (Fin 4) ℝ) j i = -X.1 i j := by
  have h := (LieAlgebra.Orthogonal.mem_so _ _ _).1 X.2
  exact congr_fun (congr_fun h i) j

private theorem join_split (X : SoFour) : join (splitCoordinates X.1) = X := by
  have diag (i : Fin 4) : X.1 i i = 0 := by linarith only [skew_entry X i i]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [join, joinCoordinates, splitCoordinates, diag, skew_entry X 0 1,
      skew_entry X 0 2, skew_entry X 0 3, skew_entry X 1 2, skew_entry X 1 3,
      skew_entry X 2 3]

private theorem split_join (v : VectorThree × VectorThree) : splitCoordinates (join v).1 = v := by
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [join, joinCoordinates, splitCoordinates] <;> ring

private theorem split_bracket (X Y : SoFour) :
    splitCoordinates ((⁅X, Y⁆ : SoFour).1) =
      (crossProduct (splitCoordinates X.1).1 (splitCoordinates Y.1).1,
       crossProduct (splitCoordinates X.1).2 (splitCoordinates Y.1).2) := by
  obtain ⟨x, rfl⟩ : ∃ x, X = join x := ⟨_, (join_split X).symm⟩
  obtain ⟨y, rfl⟩ : ∃ y, Y = join y := ⟨_, (join_split Y).symm⟩
  rw [split_join, split_join]
  change splitCoordinates (joinCoordinates x * joinCoordinates y -
    joinCoordinates y * joinCoordinates x) = _
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [splitCoordinates, joinCoordinates, cross_apply] <;>
    ring

/-- The two oriented three-dimensional cross-product factors, with the inverse using the sum
and difference of the factors as coordinates on the skew matrix. -/
def splitSoFour : SoFour ≃ₗ⁅ℝ⁆ VectorThree × VectorThree where
  toFun X := splitCoordinates X.1
  invFun := join
  left_inv := join_split
  right_inv := split_join
  map_add' X Y := by
    change splitCoordinates (X.1 + Y.1) = splitCoordinates X.1 + splitCoordinates Y.1
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [splitCoordinates] <;> ring
  map_smul' c X := by
    change splitCoordinates (c • X.1) = c • splitCoordinates X.1
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [splitCoordinates, smul_eq_mul] <;> ring
  map_lie' := by intro X Y; exact split_bracket X Y

end OmegaMath.OrthogonalFourSplit

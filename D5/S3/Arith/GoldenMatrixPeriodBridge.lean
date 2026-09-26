/- GID: D5/S3/Arith/GoldenMatrixPeriodBridge
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenMatrixPeriodBridge
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Golden residues embed as multiplication matrices.
   The golden generator becomes the Fibonacci matrix. -/

import D5.S3.Arith.GoldenApparition
import Mathlib.Data.Matrix.Reflection
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace D5.S3.Arith.GoldenMatrixPeriodBridge

open scoped Matrix
open D5.S3.Arith.GoldenApparition

private def multiplicationMatrix (m : ℕ) (z : GoldenMod m) :
    Matrix (Fin 2) (Fin 2) (ZMod m) :=
  !![z.a + z.b, z.b; z.b, z.a]

/-- Multiplication by a golden residue on the basis `(phi, 1)`. -/
def goldenMatrixHom (m : ℕ) :
    GoldenMod m →+* Matrix (Fin 2) (Fin 2) (ZMod m) where
  toFun := multiplicationMatrix m
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [multiplicationMatrix]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [multiplicationMatrix]
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [multiplicationMatrix, add_left_comm, add_comm]
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [multiplicationMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The matrix representation loses no residue information, and the golden
generator acts by the same Fibonacci matrix used for the period clock. -/
theorem golden_matrix_faithful (m : ℕ) :
    Function.Injective (goldenMatrixHom m) ∧
      goldenMatrixHom m (GoldenMod.phi : GoldenMod m) = !![1, 1; 1, 0] ∧
      orderOf (GoldenMod.phi : GoldenMod m) =
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
  have hinj : Function.Injective (goldenMatrixHom m) := by
    intro x y h
    apply GoldenMod.ext
    · have h11 := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 1 1) h
      simpa [goldenMatrixHom, multiplicationMatrix] using h11
    · have h01 := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 0 1) h
      simpa [goldenMatrixHom, multiplicationMatrix] using h01
  have hphi : goldenMatrixHom m (GoldenMod.phi : GoldenMod m) =
      !![1, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [goldenMatrixHom, multiplicationMatrix, GoldenMod.phi]
  refine ⟨hinj, hphi, ?_⟩
  have horder := orderOf_injective (goldenMatrixHom m).toMonoidHom
    hinj (GoldenMod.phi : GoldenMod m)
  change orderOf (goldenMatrixHom m (GoldenMod.phi : GoldenMod m)) = _ at horder
  rw [hphi] at horder
  exact horder.symm

end D5.S3.Arith.GoldenMatrixPeriodBridge

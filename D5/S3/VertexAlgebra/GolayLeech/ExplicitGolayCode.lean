/- GID: D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GolayLeech/ExplicitGolayCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The polynomial extended binary Golay code has certified weight constraints. -/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayCode

open scoped BigOperators

abbrev Binary := ZMod 2
abbrev Word := Fin 24 → Binary
abbrev Message := Fin 12 → Binary

def polynomialGenerator (axis : Fin 24) (position : Fin 12) : Binary :=
  if axis.val = 23 then 1
  else if position.val ≤ axis.val ∧
      axis.val - position.val ∈ ({0, 1, 5, 6, 7, 9, 11} : Finset ℕ) then 1 else 0

def generator : Matrix (Fin 24) (Fin 12) Binary :=
  !![  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
  1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
  0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
  1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0;
  1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0;
  1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0;
  0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0;
  1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0;
  0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0;
  1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1;
  0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1;
  0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0;
  0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0;
  0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0;
  0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1;
  0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1;
  0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1;
  0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
  1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem polynomial_generator_certificate : generator = polynomialGenerator := by
  ext axis position
  fin_cases axis <;> fin_cases position <;> decide

def encode : Message →ₗ[Binary] Word := Matrix.mulVecLin generator

def code : Submodule Binary Word := LinearMap.range encode

def weight (word : Word) : ℕ := ∑ axis, (word axis).val

theorem finite_all_ones_certificate :
    ∃ message : Message, encode message = fun _ => 1 := by
  refine ⟨![1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1], ?_⟩
  decide

theorem finite_generator_orthogonality :
    ∀ left right : Fin 12,
      (∑ axis, generator axis left * generator axis right) = 0 := by
  decide

theorem code_contains_all_ones : (fun _ => 1 : Word) ∈ code :=
  finite_all_ones_certificate

theorem encode_injective : Function.Injective encode := by
  let head : Matrix (Fin 12) (Fin 12) Binary :=
    fun axis position => generator ⟨axis.val, by omega⟩ position
  have checked : ∀ axis position : Fin 12, axis < position → head axis position = 0 := by decide
  have triangular : head.IsLowerTriangular := fun {_ _} condition => checked _ _ condition
  have determinant : head.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ triangular]
    norm_num [Fin.prod_univ_succ, head, generator, Matrix.of_apply]
  have injective := Matrix.mulVec_injective_of_det_ne_zero
    (show head.det ≠ 0 by rw [determinant]; exact one_ne_zero)
  intro left right equal
  apply injective
  ext axis
  exact congrFun equal ⟨axis.val, by omega⟩

def joinedMessage (lowerHalf tail : Fin 6 → Binary) : Message :=
  fun position => if lower : position.val < 6 then lowerHalf ⟨position.val, lower⟩
    else tail ⟨position.val - 6, by omega⟩

def packedPrefix (block : Fin 64) : Fin 6 → Binary :=
  fun position => ((block.val / 2 ^ position.val : ℕ) : Binary)

end D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayCode

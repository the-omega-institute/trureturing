/- GID: D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayDuality
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GolayLeech/ExplicitGolayDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The explicit parity-extended polynomial code is self-dual of dimension twelve. -/
import D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayCode
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayDuality

open ExplicitGolayCode
open scoped BigOperators Matrix

noncomputable def dotForm : LinearMap.BilinForm Binary Word :=
  (1 : Matrix (Fin 24) (Fin 24) Binary).toBilin'

theorem code_finrank : Module.finrank Binary code = 12 := by
  rw [code, LinearMap.finrank_range_of_inj encode_injective]
  simp [Message, Module.finrank_fintype_fun_eq_card]

theorem code_cardinality : Nat.card code = 4096 := by
  rw [code, ← Nat.card_congr (LinearEquiv.ofInjective encode encode_injective).toEquiv]
  simp [Message, Nat.card_eq_fintype_card, Fintype.card_fun, Binary]

theorem code_self_orthogonal (left right : Word) (left_member : left ∈ code)
    (right_member : right ∈ code) : dotForm left right = 0 := by
  obtain ⟨left_message, rfl⟩ := left_member
  obtain ⟨right_message, rfl⟩ := right_member
  have zero_matrix : generatorᵀ * generator = (0 : Matrix (Fin 12) (Fin 12) Binary) := by
    ext left right
    exact finite_generator_orthogonality left right
  simp only [dotForm, Matrix.toBilin'_apply', Matrix.one_mulVec, encode,
    Matrix.mulVecLin_apply]
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, zero_matrix]
  simp

theorem code_self_dual : dotForm.orthogonal code = code := by
  have inclusion : code ≤ dotForm.orthogonal code := by
    intro word member other other_member
    exact code_self_orthogonal other word other_member member
  have nondegenerate : dotForm.Nondegenerate := by
    change (1 : Matrix (Fin 24) (Fin 24) Binary).toBilin'.Nondegenerate
    exact (Matrix.nondegenerate_of_det_ne_zero (by simp :
      (1 : Matrix (Fin 24) (Fin 24) Binary).det ≠ 0)).toBilin'
  have dimension : Module.finrank Binary (dotForm.orthogonal code) = 12 := by
    rw [LinearMap.BilinForm.finrank_orthogonal nondegenerate, code_finrank]
    simp [Word, Module.finrank_fintype_fun_eq_card]
  exact (Submodule.eq_of_le_of_finrank_eq inclusion (code_finrank.trans dimension.symm)).symm

end D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayDuality

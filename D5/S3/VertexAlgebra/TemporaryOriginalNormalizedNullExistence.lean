import D5.S3.QuadraticForms.IsotropicSeparation
import D5.S3.QuadraticForms.HyperbolicFrame
import D5.S3.VertexAlgebra.TemporaryOriginalQuartet05
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents Module

private theorem actual_normalized_frame_exists
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (rank : 2 ≤ D.rank) (beta : Charge D) (charge_nonzero : beta ≠ 0) :
    ∃ (nullDirection : Fin D.rank → ℂ)
      (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
      (xAxis yAxis : Fin D.rank),
      gramPair D nullDirection nullDirection = 0 ∧
      chosenP D beta nullDirection ≠ 0 ∧
      inverse * frame = 1 ∧ frame * inverse = 1 ∧ xAxis ≠ yAxis ∧
      frame xAxis = nullDirection ∧ frame yAxis = adaptedPartner D beta nullDirection ∧
      (∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0) ∧
      (∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) ∧
      gramPair D (adaptedPartner D beta nullDirection) nullDirection = 1 ∧
      gramPair D (adaptedPartner D beta nullDirection)
        (adaptedPartner D beta nullDirection) = 0 ∧
      complexCharge D beta =
        chosenP D beta nullDirection • adaptedPartner D beta nullDirection +
          chosenQ D beta nullDirection • nullDirection := by
  classical
  let form := Matrix.toBilin' (gramComplex D)
  have literal (left right : Fin D.rank → ℂ) : form left right = gramPair D left right := by
    exact Matrix.toBilin'_apply (gramComplex D) left right
  have symmetric : LinearMap.IsSymm form := ⟨fun left right => by
    simpa only [RingHom.id_apply, literal] using gramPair_symm D left right⟩
  have nondegenerate : LinearMap.Nondegenerate form :=
    Matrix.nondegenerate_toBilin'_iff.mpr
      (Matrix.nondegenerate_of_det_ne_zero (Matrix.det_ne_zero_of_left_inverse leftGramInverse))
  have embedding_injective : Function.Injective (complexCharge D) := by
    intro first second equality
    funext index
    exact Int.cast_injective (congrFun equality index)
  have embedding_nonzero : complexCharge D beta ≠ 0 := by
    intro vanished
    apply charge_nonzero
    apply embedding_injective
    have embedding_zero : complexCharge D (0 : Charge D) = 0 := by
      funext index
      change ((0 : ℤ) : ℂ) = 0
      exact Int.cast_zero
    exact vanished.trans embedding_zero.symm
  let functional := form.flip (complexCharge D beta)
  have functional_nonzero : functional ≠ 0 := by
    intro vanished
    apply embedding_nonzero
    apply nondegenerate.2
    intro vector
    change functional vector = 0
    have coefficient := congrArg (fun linear : (Fin D.rank → ℂ) →ₗ[ℂ] ℂ => linear vector) vanished
    exact coefficient
  have dimension : 2 ≤ finrank ℂ (Fin D.rank → ℂ) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using rank
  obtain ⟨direction, null, detected⟩ :=
    D5.S3.QuadraticForms.IsotropicSeparation.exists_null_detected_by_linear_form
      form symmetric nondegenerate.1 dimension functional functional_nonzero
  have null_literal : gramPair D direction direction = 0 := (literal direction direction).symm.trans null
  have chosen_nonzero : chosenP D beta direction ≠ 0 := by
    change gramPair D direction (complexCharge D beta) ≠ 0
    change form direction (complexCharge D beta) ≠ 0 at detected
    rwa [literal] at detected
  have partner := adaptedPartner_relations D beta direction null_literal chosen_nonzero
  obtain ⟨frame, inverse, xAxis, yAxis, leftInverse, rightInverse, distinct,
      xRow, yRow, xDual, yDual⟩ :=
    D5.S3.QuadraticForms.HyperbolicFrame.exists_frame_with_literal_duals
      form symmetric direction (adaptedPartner D beta direction) null
      ((literal _ _).trans partner.2.1) ((literal _ _).trans partner.1)
  exact ⟨direction, frame, inverse, xAxis, yAxis, null_literal, chosen_nonzero,
    leftInverse, rightInverse, distinct, xRow, yRow,
    (by simpa only [literal] using xDual),
    (by simpa only [literal] using yDual), partner⟩

example (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (critical : D.rank = 26) (beta : Charge D) (charge_nonzero : beta ≠ 0) :
    ∃ (nullDirection : Fin D.rank → ℂ)
      (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
      (xAxis yAxis : Fin D.rank),
      gramPair D nullDirection nullDirection = 0 ∧ chosenP D beta nullDirection ≠ 0 ∧
      inverse * frame = 1 ∧ frame * inverse = 1 ∧ xAxis ≠ yAxis ∧
      frame xAxis = nullDirection ∧ frame yAxis = adaptedPartner D beta nullDirection ∧
      (∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0) ∧
      (∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) ∧
      gramPair D (adaptedPartner D beta nullDirection) nullDirection = 1 ∧
      gramPair D (adaptedPartner D beta nullDirection)
        (adaptedPartner D beta nullDirection) = 0 ∧
      complexCharge D beta =
        chosenP D beta nullDirection • adaptedPartner D beta nullDirection +
          chosenQ D beta nullDirection • nullDirection := by
  exact actual_normalized_frame_exists D H leftGramInverse rightGramInverse
    (by omega) beta charge_nonzero

end D5.S3.VertexAlgebra.OriginalQQuartetSource

import D5.S3.QuadraticForms.IsotropicSeparation
import D5.S3.VertexAlgebra.OriginalQActualQuotientTransferTransient
import D5.S3.VertexAlgebra.OriginalQTransferredMassShellTransient
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeSugawaraVirasoro
  LatticeBcGhostBrstCharge BcGhostFockSupport
open OriginalQFiniteHplCheck
open Module Submodule LinearMap.BilinForm
open scoped BigOperators TensorProduct

noncomputable section

private theorem literal_dual_frame
    {Scalar : Type*} [Field Scalar] {dimension : ℕ}
    (form : LinearMap.BilinForm Scalar (Fin dimension → Scalar))
    (symmetric : LinearMap.IsSymm form)
    (first second : Fin dimension → Scalar)
    (firstNull : form first first = 0) (secondNull : form second second = 0)
    (paired : form second first = 1) :
    ∃ (frame inverse : Matrix (Fin dimension) (Fin dimension) Scalar)
      (firstAxis secondAxis : Fin dimension),
      inverse * frame = 1 ∧ frame * inverse = 1 ∧ firstAxis ≠ secondAxis ∧
      frame firstAxis = first ∧ frame secondAxis = second ∧
      (∀ row, form (frame secondAxis) (frame row) = if row = firstAxis then 1 else 0) ∧
      (∀ row, form (frame firstAxis) (frame row) = if row = secondAxis then 1 else 0) := by
  classical
  have opposite : form first second = 1 := (symmetric.eq first second).trans paired
  have firstNonzero : first ≠ 0 := by
    intro zero
    simpa [zero] using paired
  have independent : LinearIndependent Scalar ![first, second] := by
    rw [LinearIndependent.pair_iff' firstNonzero]
    intro scalar equality
    have contradiction := congrArg (form first) equality
    simp only [map_smul, smul_eq_mul, firstNull, mul_zero, opposite] at contradiction
    exact zero_ne_one contradiction
  let plane := span Scalar (Set.range ![first, second])
  have firstMember : first ∈ plane := subset_span ⟨0, rfl⟩
  have secondMember : second ∈ plane := subset_span ⟨1, rfl⟩
  have reflexive : LinearMap.IsRefl form := symmetric.isRefl
  have planeNondegenerate : LinearMap.Nondegenerate (form.restrict plane) := by
    apply (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (reflexive.domRestrict plane)).mpr
    intro vector vanished
    obtain ⟨coefficients, expansion⟩ :=
      (mem_span_range_iff_exists_fun Scalar).mp vector.property
    have firstCoefficient : coefficients 0 = 0 := by
      have equation := vanished ⟨second, secondMember⟩
      change form (vector : Fin dimension → Scalar) second = 0 at equation
      rw [← expansion] at equation
      simpa [Fin.sum_univ_two, opposite, secondNull] using equation
    have secondCoefficient : coefficients 1 = 0 := by
      have equation := vanished ⟨first, firstMember⟩
      change form (vector : Fin dimension → Scalar) first = 0 at equation
      rw [← expansion] at equation
      simpa [Fin.sum_univ_two, firstNull, paired] using equation
    apply Subtype.ext
    rw [← expansion]
    simp [Fin.sum_univ_two, firstCoefficient, secondCoefficient]
  have complementary : IsCompl plane (form.orthogonal plane) :=
    isCompl_orthogonal_of_restrict_nondegenerate reflexive planeNondegenerate
  let complement := form.orthogonal plane
  let planeBasis := Basis.span independent
  have planeRows (index : Fin 2) : (planeBasis index : Fin dimension → Scalar) =
      ![first, second] index := congrArg Subtype.val (Basis.span_apply independent index)
  let complementBasis := Module.finBasis Scalar complement
  let combined := (planeBasis.prod complementBasis).map
    (Submodule.prodEquivOfIsCompl plane complement complementary)
  have planeRow (index : Fin 2) : combined (Sum.inl index) = ![first, second] index := by
    simp [combined, Basis.map_apply, Basis.prod_apply, planeRows]
  have complementRow (index : Fin (finrank Scalar complement)) :
      combined (Sum.inr index) = (complementBasis index : Fin dimension → Scalar) := by
    simp [combined, Basis.map_apply, Basis.prod_apply]
  have firstOrthogonal (index : Fin (finrank Scalar complement)) :
      form first (combined (Sum.inr index)) = 0 := by
    rw [complementRow]
    exact mem_orthogonal_iff.mp (complementBasis index).property first firstMember
  have secondOrthogonal (index : Fin (finrank Scalar complement)) :
      form second (combined (Sum.inr index)) = 0 := by
    rw [complementRow]
    exact mem_orthogonal_iff.mp (complementBasis index).property second secondMember
  have firstDual (row : Fin 2 ⊕ Fin (finrank Scalar complement)) :
      form second (combined row) = if row = Sum.inl 0 then 1 else 0 := by
    rcases row with index | index
    · fin_cases index <;> simp [planeRow, paired, secondNull]
    · simp [secondOrthogonal]
  have secondDual (row : Fin 2 ⊕ Fin (finrank Scalar complement)) :
      form first (combined row) = if row = Sum.inl 1 then 1 else 0 := by
    rcases row with index | index
    · fin_cases index <;> simp [planeRow, firstNull, opposite]
    · simp [firstOrthogonal]
  have cardinality : Fintype.card (Fin 2 ⊕ Fin (finrank Scalar complement)) = dimension := by
    rw [← Module.finrank_eq_card_basis combined, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  let indices := Fintype.equivFinOfCardEq cardinality
  let basis := combined.reindex indices
  let firstAxis := indices (Sum.inl 0)
  let secondAxis := indices (Sum.inl 1)
  have firstRow : basis firstAxis = first := by
    simp [basis, firstAxis, Basis.reindex_apply, planeRow]
  have secondRow : basis secondAxis = second := by
    simp [basis, secondAxis, Basis.reindex_apply, planeRow]
  let standard := Pi.basisFun Scalar (Fin dimension)
  let frame := (LinearMap.toMatrix basis standard LinearMap.id).transpose
  let inverse := (LinearMap.toMatrix standard basis LinearMap.id).transpose
  have rowEquation (row : Fin dimension) : frame row = basis row := by
    ext column
    change LinearMap.toMatrix basis standard LinearMap.id column row = basis row column
    rw [LinearMap.toMatrix_apply]
    simp [standard, Pi.basisFun_repr]
  have leftInverse : inverse * frame = 1 := by
    change (LinearMap.toMatrix standard basis LinearMap.id).transpose *
      (LinearMap.toMatrix basis standard LinearMap.id).transpose = 1
    rw [← Matrix.transpose_mul, ← LinearMap.toMatrix_comp standard basis standard]
    simp [LinearMap.toMatrix_id]
  have rightInverse : frame * inverse = 1 := by
    change (LinearMap.toMatrix basis standard LinearMap.id).transpose *
      (LinearMap.toMatrix standard basis LinearMap.id).transpose = 1
    rw [← Matrix.transpose_mul, ← LinearMap.toMatrix_comp basis standard basis]
    simp [LinearMap.toMatrix_id]
  refine ⟨frame, inverse, firstAxis, secondAxis, leftInverse, rightInverse, ?_,
    (rowEquation firstAxis).trans firstRow, (rowEquation secondAxis).trans secondRow, ?_, ?_⟩
  · intro equality
    have same := indices.injective equality
    simpa using same
  · intro row
    rw [rowEquation, secondRow, rowEquation]
    have dual := firstDual (indices.symm row)
    simpa [basis, Basis.reindex_apply, firstAxis, indices.symm_apply_eq] using dual
  · intro row
    rw [rowEquation, firstRow, rowEquation]
    have dual := secondDual (indices.symm row)
    simpa [basis, Basis.reindex_apply, secondAxis, indices.symm_apply_eq] using dual

private theorem actual_nonzero_charge_frame
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
    literal_dual_frame form symmetric direction (adaptedPartner D beta direction) null
      ((literal _ _).trans partner.2.1) ((literal _ _).trans partner.1)
  exact ⟨direction, frame, inverse, xAxis, yAxis, null_literal, chosen_nonzero,
    leftInverse, rightInverse, distinct, xRow, yRow,
    (by simpa only [literal] using xDual),
    (by simpa only [literal] using yDual), partner⟩

theorem actual_nonzero_charge_original_q_transfer
    (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (critical : D.rank = 26) (beta : Charge D) (charge_nonzero : beta ≠ 0)
    (level : ℤ) :
    ∃ (nullDirection : Fin D.rank → ℂ)
      (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
      (xAxis yAxis : Fin D.rank),
      gramPair D nullDirection nullDirection = 0 ∧
      chosenP D beta nullDirection ≠ 0 ∧
      ∃ (leftFrameInverse : inverse * frame = 1)
        (rightFrameInverse : frame * inverse = 1),
        xAxis ≠ yAxis ∧
        frame xAxis = nullDirection ∧ frame yAxis = adaptedPartner D beta nullDirection ∧
        (∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0) ∧
        (∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) ∧
        gramPair D (adaptedPartner D beta nullDirection) nullDirection = 1 ∧
        gramPair D (adaptedPartner D beta nullDirection)
          (adaptedPartner D beta nullDirection) = 0 ∧
        complexCharge D beta =
          chosenP D beta nullDirection • adaptedPartner D beta nullDirection +
            chosenQ D beta nullDirection • nullDirection ∧
        (∃ (originalSquare :
            energyOriginalQ D H leftGramInverse rightGramInverse beta level *
              energyOriginalQ D H leftGramInverse rightGramInverse beta level = 0)
          (reducedSquare :
            energyReducedDifferential D H frame inverse leftGramInverse rightGramInverse
              leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level *
              energyReducedDifferential D H frame inverse leftGramInverse rightGramInverse
                leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level = 0),
          Nonempty (trueCohomology (Source := LinearMap.range
            (energyProjector D H frame inverse leftGramInverse rightGramInverse
              leftFrameInverse rightFrameInverse beta xAxis yAxis level))
            (energyReducedDifferential D H frame inverse leftGramInverse rightGramInverse
              leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level) reducedSquare ≃ₗ[ℂ]
            trueCohomology (Source := originalEnergySector D H beta level)
              (energyOriginalQ D H leftGramInverse rightGramInverse beta level) originalSquare)) ∧
        (∀ (state : State D), chargeProjection D beta state = state →
        (M D H 0 + G D 0) state = (chosenH D beta + (level : ℂ) - 1) • state →
          finiteOriginalTransferredDifferential D H frame inverse leftFrameInverse rightFrameInverse
            beta nullDirection xAxis yAxis level state =
            (chosenH D beta + (level : ℂ) - 1) •
              C D 0 (P D frame inverse leftFrameInverse rightFrameInverse xAxis yAxis state)) := by
  obtain ⟨nullDirection, frame, inverse, xAxis, yAxis, null, nonzero,
      leftFrameInverse, rightFrameInverse, distinct, xRow, yRow, xDual, yDual,
      partner⟩ := actual_nonzero_charge_frame D H leftGramInverse rightGramInverse
    (by omega) beta charge_nonzero
  have transfer := original_energy_true_quotient_transfer D H frame inverse leftGramInverse
    rightGramInverse leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis level
    critical null nonzero distinct xRow yRow xDual yDual
  refine ⟨nullDirection, frame, inverse, xAxis, yAxis, null, nonzero,
    leftFrameInverse, rightFrameInverse, distinct, xRow, yRow, xDual, yDual,
    partner.1, partner.2.1, partner.2.2, transfer, ?_⟩
  intro state sector energy
  exact original_transferred_differential_mass_shell D H frame inverse leftGramInverse rightGramInverse
    leftFrameInverse rightFrameInverse beta nullDirection xAxis yAxis null nonzero distinct
    xRow yRow xDual yDual level state sector energy

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource

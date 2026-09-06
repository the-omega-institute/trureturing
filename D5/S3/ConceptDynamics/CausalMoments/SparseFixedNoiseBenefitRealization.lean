/- GID: D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds]
   digest: Componentwise table compression preserves independent mechanism laws, all selected response cells, and the exact covariate joint-benefit image using at most 3k+1 support points per mechanism. -/

import D5.S3.ConceptDynamics.CausalMoments.ReducedResponseTableMoments
import D5.S3.ConceptDynamics.CausalMoments.FixedNoiseCovariateBenefitSharpBounds

/- Library audit (2026-09-06): reuse FixedNoisePairModel, selectedPairLaw_mass,
   HasConditionalFourMarginals, and the existing sharp interval theorem.
   Each complete mechanism law is compressed separately. Their product is then
   formed by the unchanged model semantics. No convex mixture of product laws
   or cross-world coordinate independence is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.CausalMoments.SparseFixedNoiseBenefitRealization

open scoped BigOperators
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianBenefitIdentificationBoundary
open D5.S3.ConceptDynamics.CausalMoments.FiniteConditionalResponseTable
open D5.S3.ConceptDynamics.CausalMoments.FixedNoiseCovariateBenefitSharpBounds
open D5.S3.ConceptDynamics.CausalMoments.ReducedResponseTableMoments

variable {Covariate : Type*} [Fintype Covariate] [DecidableEq Covariate]

/-- Componentwise replacement retains the full selected-pair distribution and
all response rows, with at most 3k+1 nonzero table atoms per mechanism. -/
theorem exists_fixedNoise_sparse_equivalent
    (weight : FiniteResponseLaw Covariate)
    (model : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool)) :
    ∃ sparse : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool),
      (finiteLawSupport sparse.leftTableLaw).card ≤ 3 * Fintype.card Covariate + 1 ∧
      (finiteLawSupport sparse.rightTableLaw).card ≤ 3 * Fintype.card Covariate + 1 ∧
      (∀ c, (tableEvaluationLaw sparse.leftTableLaw c).mass =
        (tableEvaluationLaw model.leftTableLaw c).mass) ∧
      (∀ c, (tableEvaluationLaw sparse.rightTableLaw c).mass =
        (tableEvaluationLaw model.rightTableLaw c).mass) ∧
      (selectedPairLaw weight sparse).mass = (selectedPairLaw weight model).mass := by
  obtain ⟨left, left_card, left_rows⟩ := exists_three_cell_table_compression model.leftTableLaw
  obtain ⟨right, right_card, right_rows⟩ := exists_three_cell_table_compression model.rightTableLaw
  let sparse : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool) := ⟨left, right⟩
  refine ⟨sparse, left_card, right_card, left_rows, right_rows, ?_⟩
  funext response
  rcases response with ⟨c, first, second⟩
  rw [selectedPairLaw_mass, selectedPairLaw_mass]
  change weight.mass c * ((tableEvaluationLaw left c).mass first *
    (tableEvaluationLaw right c).mass second) = _
  rw [left_rows, right_rows]

/-- The complete two-mechanism disturbance product has polynomial support once
both table laws obey the componentwise bound. The covariate root is separate. -/
theorem fixedNoise_pair_support_card_le
    (model : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool))
    (left_card : (finiteLawSupport model.leftTableLaw).card ≤ 3 * Fintype.card Covariate + 1)
    (right_card : (finiteLawSupport model.rightTableLaw).card ≤ 3 * Fintype.card Covariate + 1) :
    (finiteLawSupport (productResponseLaw model.leftTableLaw model.rightTableLaw)).card ≤
      (3 * Fintype.card Covariate + 1) ^ 2 := by
  classical
  have support_eq : finiteLawSupport (productResponseLaw model.leftTableLaw model.rightTableLaw) =
      finiteLawSupport model.leftTableLaw ×ˢ finiteLawSupport model.rightTableLaw := by
    ext response
    rcases response with ⟨left, right⟩
    simp [finiteLawSupport, productResponseLaw, productResponseMass, mul_ne_zero_iff]
  rw [support_eq, Finset.card_product, pow_two]
  exact Nat.mul_le_mul left_card right_card

/-- Restricting to these small independent table laws preserves the entire
identified query image, including every interior target and each endpoint. -/
theorem fixedNoise_sparse_attainment_iff
    (weight : FiniteResponseLaw Covariate)
    (p10 p11 p20 p21 : Covariate → ℚ) (target : ℚ) :
    (∃ model : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool),
      HasConditionalFourMarginals model p10 p11 p20 p21 ∧
      fixedNoiseJointBenefit weight model = target) ↔
    (∃ model : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool),
      (finiteLawSupport model.leftTableLaw).card ≤ 3 * Fintype.card Covariate + 1 ∧
      (finiteLawSupport model.rightTableLaw).card ≤ 3 * Fintype.card Covariate + 1 ∧
      HasConditionalFourMarginals model p10 p11 p20 p21 ∧
      fixedNoiseJointBenefit weight model = target) := by
  constructor
  · rintro ⟨model, marginals, value⟩
    obtain ⟨sparse, left_card, right_card, left_rows, right_rows, selected_eq⟩ :=
      exists_fixedNoise_sparse_equivalent weight model
    refine ⟨sparse, left_card, right_card, ?_, ?_⟩
    · intro c
      have row_marginals := marginals c
      dsimp only [fixedNoiseStratumModel] at row_marginals ⊢
      rw [left_rows, right_rows]
      exact row_marginals
    · unfold fixedNoiseJointBenefit at value ⊢
      rw [selected_eq]
      exact value
  · rintro ⟨model, _, _, marginals, value⟩
    exact ⟨model, marginals, value⟩

/-- The previously established exact rational interval has attaining models
whose two independent table disturbances each have support at most 3k+1. -/
theorem fixedNoise_sparse_joint_benefit_sharp_iff
    (weight : FiniteResponseLaw Covariate)
    (p10 p11 p20 p21 : Covariate → ℚ) (target : ℚ)
    (first_compatible : ∀ c, max 0 (p11 c - p10 c) ≤ min (p11 c) (1 - p10 c))
    (second_compatible : ∀ c, max 0 (p21 c - p20 c) ≤ min (p21 c) (1 - p20 c)) :
    ((∑ c, weight.mass c * (max 0 (p11 c - p10 c) * max 0 (p21 c - p20 c))) ≤ target ∧
      target ≤ ∑ c, weight.mass c * (min (p11 c) (1 - p10 c) * min (p21 c) (1 - p20 c))) ↔
    (∃ model : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool),
      (finiteLawSupport model.leftTableLaw).card ≤ 3 * Fintype.card Covariate + 1 ∧
      (finiteLawSupport model.rightTableLaw).card ≤ 3 * Fintype.card Covariate + 1 ∧
      HasConditionalFourMarginals model p10 p11 p20 p21 ∧
      fixedNoiseJointBenefit weight model = target) :=
  (fixedNoise_covariate_joint_benefit_sharp_iff weight p10 p11 p20 p21 target
    first_compatible second_compatible).trans
      (fixedNoise_sparse_attainment_iff weight p10 p11 p20 p21 target)

#print axioms exists_fixedNoise_sparse_equivalent
#print axioms fixedNoise_pair_support_card_le
#print axioms fixedNoise_sparse_joint_benefit_sharp_iff

end D5.S3.ConceptDynamics.CausalMoments.SparseFixedNoiseBenefitRealization

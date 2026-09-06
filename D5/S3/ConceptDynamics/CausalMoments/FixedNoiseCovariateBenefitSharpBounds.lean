/- GID: D5/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/FixedNoiseCovariateBenefitSharpBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conditional four-marginal joint-benefit intervals aggregate sharply in one independent fixed-table-noise model, with explicit rational scalar interpolation and simultaneous structural witnesses. -/

import D5.S3.ConceptDynamics.CausalMoments.FiniteConditionalResponseTable
import D5.S3.ConceptDynamics.CausalMoments.MarkovianJointBenefitMarginalSharpBounds

/- Library audit (2026-09-06): reuse the existing per-stratum four-marginal
   sharpness theorem and the full response-table realization. The existing
   CovariateSharpAggregation theorem is Real-valued and assumes independent
   stratum selection. A private rational interpolation proof keeps all witnesses
   in the rational source-law carrier; simultaneous selection is discharged by
   constructing two complete table laws independent of the covariate root.
   Cross-row independence is a witness choice, not a model-class restriction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.CausalMoments.FixedNoiseCovariateBenefitSharpBounds

open scoped BigOperators
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianBenefitIdentificationBoundary
open D5.S3.ConceptDynamics.CausalMoments.MarkovianJointMechanismBenefitSharpBounds
open D5.S3.ConceptDynamics.CausalMoments.MarkovianJointBenefitMarginalSharpBounds
open D5.S3.ConceptDynamics.CausalMoments.FiniteConditionalResponseTable

variable {Covariate : Type*} [Fintype Covariate] [DecidableEq Covariate]

/-- A fixed structural equation reads the same table disturbance under both
constant treatment interventions. Covariate is an independent source root. -/
def fixedNoiseOutcome (c : Covariate) (treatment : Bool)
    (table : Covariate → Bool × Bool) : Bool :=
  if treatment then (table c).2 else (table c).1

/-- The complete treatment response is precisely the selected table row. -/
theorem fixedNoiseOutcome_response (c : Covariate) (table : Covariate → Bool × Bool) :
    (fixedNoiseOutcome c false table, fixedNoiseOutcome c true table) = table c := by
  simp [fixedNoiseOutcome]

/-- The two actual response marginals in one covariate stratum of a fixed model. -/
noncomputable def fixedNoiseStratumModel
    (model : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool))
    (c : Covariate) : MarkovianJointMechanismModel where
  firstLaw := tableEvaluationLaw model.leftTableLaw c
  secondLaw := tableEvaluationLaw model.rightTableLaw c

/-- The four prescribed conditional intervention kernels. Values in zero-mass
strata are kernel specifications, not observationally identified conditionals. -/
def HasConditionalFourMarginals
    (model : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool))
    (p10 p11 p20 p21 : Covariate → ℚ) : Prop :=
  ∀ c,
    controlSuccessMarginal (fixedNoiseStratumModel model c).firstLaw.mass = p10 c ∧
    treatmentSuccessMarginal (fixedNoiseStratumModel model c).firstLaw.mass = p11 c ∧
    controlSuccessMarginal (fixedNoiseStratumModel model c).secondLaw.mass = p20 c ∧
    treatmentSuccessMarginal (fixedNoiseStratumModel model c).secondLaw.mass = p21 c

/-- Population simultaneous benefit computed from the actual common-source law. -/
noncomputable def fixedNoiseJointBenefit
    (weight : FiniteResponseLaw Covariate)
    (model : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool)) : ℚ :=
  ∑ c, (selectedPairLaw weight model).mass (c, ((false, true), (false, true)))

/-- The structural query is the weighted average of within-stratum products. -/
theorem fixedNoiseJointBenefit_eq_weighted
    (weight : FiniteResponseLaw Covariate)
    (model : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool)) :
    fixedNoiseJointBenefit weight model =
      ∑ c, weight.mass c *
        jointMechanismBenefitMass (markovianJointResponseMass (fixedNoiseStratumModel model c)) := by
  unfold fixedNoiseJointBenefit
  apply Finset.sum_congr rfl
  intro c _
  rw [selectedPairLaw_mass, markovianJointBenefit_eq_product] <;> rfl

/-- Every family of independent-mechanism stratum response laws has one fixed
pair of full-table disturbances with exactly those row marginals. -/
theorem fixedNoiseStrata_simultaneously_realized
    (strata : Covariate → MarkovianJointMechanismModel) :
    ∃ model : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool),
      ∀ c,
        (fixedNoiseStratumModel model c).firstLaw.mass = (strata c).firstLaw.mass ∧
        (fixedNoiseStratumModel model c).secondLaw.mass = (strata c).secondLaw.mass := by
  refine ⟨canonicalFixedNoisePair (fun c => (strata c).firstLaw)
    (fun c => (strata c).secondLaw), ?_⟩
  intro c
  constructor <;>
    simp only [fixedNoiseStratumModel, canonicalFixedNoisePair, tableEvaluationLaw_independentSource]

private theorem rational_weighted_interval_witness
    (weight lower upper : Covariate → ℚ)
    (weight_nonnegative : ∀ c, 0 ≤ weight c) (ordered : ∀ c, lower c ≤ upper c)
    (target : ℚ)
    (bounds : (∑ c, weight c * lower c) ≤ target ∧ target ≤ ∑ c, weight c * upper c) :
    ∃ value : Covariate → ℚ,
      (∀ c, lower c ≤ value c ∧ value c ≤ upper c) ∧
      (∑ c, weight c * value c) = target := by
  let lo := ∑ c, weight c * lower c
  let hi := ∑ c, weight c * upper c
  have aggregate_order : lo ≤ hi :=
    Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (ordered c) (weight_nonnegative c))
  by_cases same : lo = hi
  · refine ⟨lower, (fun c => ⟨le_rfl, ordered c⟩), ?_⟩
    change lo = target
    change lo ≤ target ∧ target ≤ hi at bounds
    linarith [bounds.1, bounds.2, same]
  · have gap_positive : 0 < hi - lo := sub_pos.mpr (lt_of_le_of_ne aggregate_order same)
    let t := (target - lo) / (hi - lo)
    have t_nonnegative : 0 ≤ t := div_nonneg (sub_nonneg.mpr bounds.1) gap_positive.le
    have t_le_one : t ≤ 1 := by
      apply (div_le_iff₀ gap_positive).2
      change target - lo ≤ 1 * (hi - lo)
      change lo ≤ target ∧ target ≤ hi at bounds
      linarith [bounds.2]
    have t_identity : t * (hi - lo) = target - lo :=
      div_mul_cancel₀ (target - lo) (ne_of_gt gap_positive)
    refine ⟨(fun c => lower c + t * (upper c - lower c)), ?_, ?_⟩
    · intro c
      have gap := sub_nonneg.mpr (ordered c)
      have positive_part := mul_nonneg t_nonnegative gap
      have bounded_part := mul_le_mul_of_nonneg_right t_le_one gap
      constructor <;> nlinarith
    · calc
        (∑ c, weight c * (lower c + t * (upper c - lower c))) =
            ∑ c, (weight c * lower c + t * (weight c * upper c - weight c * lower c)) := by
          apply Finset.sum_congr rfl
          intro c _
          ring
        _ = lo + t * (hi - lo) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
        _ = target := by linarith [t_identity]

/-- Exact rational identified interval in one shared-covariate fixed-noise SCM.
Only the four conditional intervention marginals are fixed. Each full table may
have arbitrary cross-row dependence; no extra cross-stratum restrictions are imposed. -/
theorem fixedNoise_covariate_joint_benefit_sharp_iff
    (weight : FiniteResponseLaw Covariate)
    (p10 p11 p20 p21 : Covariate → ℚ) (target : ℚ)
    (first_compatible : ∀ c, max 0 (p11 c - p10 c) ≤ min (p11 c) (1 - p10 c))
    (second_compatible : ∀ c, max 0 (p21 c - p20 c) ≤ min (p21 c) (1 - p20 c)) :
    ((∑ c, weight.mass c * (max 0 (p11 c - p10 c) * max 0 (p21 c - p20 c))) ≤ target ∧
      target ≤ ∑ c, weight.mass c * (min (p11 c) (1 - p10 c) * min (p21 c) (1 - p20 c))) ↔
    ∃ model : FixedNoisePairModel Covariate (Bool × Bool) (Bool × Bool),
      HasConditionalFourMarginals model p10 p11 p20 p21 ∧
      fixedNoiseJointBenefit weight model = target := by
  let lower := fun c => max 0 (p11 c - p10 c) * max 0 (p21 c - p20 c)
  let upper := fun c => min (p11 c) (1 - p10 c) * min (p21 c) (1 - p20 c)
  have ordered : ∀ c, lower c ≤ upper c := by
    intro c
    exact mul_le_mul (first_compatible c) (second_compatible c)
      (le_max_left _ _) ((le_max_left _ _).trans (first_compatible c))
  constructor
  · intro bounds
    rcases rational_weighted_interval_witness weight.mass lower upper
      weight.nonnegative ordered target bounds with ⟨value, value_bounds, value_sum⟩
    have local_models : ∀ c, ∃ stratum : MarkovianJointMechanismModel,
        controlSuccessMarginal stratum.firstLaw.mass = p10 c ∧
        treatmentSuccessMarginal stratum.firstLaw.mass = p11 c ∧
        controlSuccessMarginal stratum.secondLaw.mass = p20 c ∧
        treatmentSuccessMarginal stratum.secondLaw.mass = p21 c ∧
        jointMechanismBenefitMass (markovianJointResponseMass stratum) = value c := by
      intro c
      exact (four_marginal_joint_benefit_sharp_iff
        (p10 c) (p11 c) (p20 c) (p21 c) (value c)
        (first_compatible c) (second_compatible c)).mp (value_bounds c)
    choose strata h10 h11 h20 h21 hj using local_models
    rcases fixedNoiseStrata_simultaneously_realized strata with ⟨model, realizes⟩
    refine ⟨model, ?_, ?_⟩
    · intro c
      rcases realizes c with ⟨left_eq, right_eq⟩
      rw [left_eq, right_eq]
      exact ⟨h10 c, h11 c, h20 c, h21 c⟩
    · rw [fixedNoiseJointBenefit_eq_weighted]
      calc
        (∑ c, weight.mass c *
          jointMechanismBenefitMass (markovianJointResponseMass (fixedNoiseStratumModel model c))) =
            ∑ c, weight.mass c * value c := by
          apply Finset.sum_congr rfl
          intro c _
          have query_eq :
              jointMechanismBenefitMass (markovianJointResponseMass (fixedNoiseStratumModel model c)) =
                jointMechanismBenefitMass (markovianJointResponseMass (strata c)) := by
            rw [markovianJointBenefit_eq_product, markovianJointBenefit_eq_product,
              (realizes c).1, (realizes c).2]
          rw [query_eq, hj c]
        _ = target := value_sum
  · rintro ⟨model, marginals, query_eq⟩
    have pointwise : ∀ c, lower c ≤
        jointMechanismBenefitMass (markovianJointResponseMass (fixedNoiseStratumModel model c)) ∧
        jointMechanismBenefitMass (markovianJointResponseMass (fixedNoiseStratumModel model c)) ≤ upper c := by
      intro c
      rcases marginals c with ⟨h10, h11, h20, h21⟩
      exact (four_marginal_joint_benefit_sharp_iff (p10 c) (p11 c) (p20 c) (p21 c)
        (jointMechanismBenefitMass (markovianJointResponseMass (fixedNoiseStratumModel model c)))
        (first_compatible c) (second_compatible c)).mpr
        ⟨fixedNoiseStratumModel model c, h10, h11, h20, h21, rfl⟩
    rw [fixedNoiseJointBenefit_eq_weighted] at query_eq
    constructor
    · calc
        (∑ c, weight.mass c * lower c) ≤ ∑ c, weight.mass c *
            jointMechanismBenefitMass (markovianJointResponseMass (fixedNoiseStratumModel model c)) :=
          Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (pointwise c).1 (weight.nonnegative c))
        _ = target := query_eq
    · calc
        target = ∑ c, weight.mass c *
            jointMechanismBenefitMass (markovianJointResponseMass (fixedNoiseStratumModel model c)) := query_eq.symm
        _ ≤ ∑ c, weight.mass c * upper c :=
          Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (pointwise c).2 (weight.nonnegative c))

#print axioms fixedNoiseOutcome_response
#print axioms fixedNoiseJointBenefit_eq_weighted
#print axioms fixedNoiseStrata_simultaneously_realized
#print axioms fixedNoise_covariate_joint_benefit_sharp_iff

end D5.S3.ConceptDynamics.CausalMoments.FixedNoiseCovariateBenefitSharpBounds

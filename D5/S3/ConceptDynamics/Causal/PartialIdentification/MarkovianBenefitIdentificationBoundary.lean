/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/MarkovianBenefitIdentificationBoundary
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/MarkovianBenefitIdentificationBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Independent treatment assignment noise leaves the Boolean benefit query at its sharp Frechet interval; factorizing the two outcome-response coordinates is a strictly stronger cross-world assumption that point identifies benefit. -/

import D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianResponseLawFactorization

/- Library-search audit trail (2026-09-04):
   * `BenefitProbabilityBounds` proves validity of the Boolean potential-outcome
     bounds, while `FiniteEventCouplingSharpBounds` supplies explicit sharp
     four-cell coupling witnesses.
   * `MarkovianResponseLawFactorization` proves product factorization across
     independent exogenous components and exact marginal recovery.
   * Repository searches found no theorem distinguishing ordinary Markovian
     independence between treatment-assignment noise and the outcome mechanism
     from the stronger cross-world independence of the two potential-outcome
     coordinates stored inside that one outcome mechanism.
   * This module proves that the former leaves the complete Frechet interval
     sharp, whereas the latter forces the benefit mass to `(1 - p0) * p1`.
   * No claim is made that response-coordinate independence follows from the
     standard Markovian SCM definition. It is exposed as an additional
     cross-world restriction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianBenefitIdentificationBoundary

open scoped BigOperators
open D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianResponseLawFactorization

/-- Success probability under the control potential outcome. -/
def controlSuccessMarginal (mass : Bool × Bool → ℚ) : ℚ :=
  mass (true, false) + mass (true, true)

/-- Success probability under the treated potential outcome. -/
def treatmentSuccessMarginal (mass : Bool × Bool → ℚ) : ℚ :=
  mass (false, true) + mass (true, true)

/-- Probability that treatment changes the outcome from false to true. -/
def benefitResponseMass (mass : Bool × Bool → ℚ) : ℚ :=
  mass (false, true)

/-- A Markovian treatment-assignment/outcome model. Assignment disturbance and
outcome-response disturbance are independent by construction. The outcome
response itself may have arbitrary dependence between its two potential
outcome coordinates. -/
structure MarkovianAssignmentOutcomeModel where
  assignmentLaw : FiniteResponseLaw Bool
  outcomeLaw : FiniteResponseLaw (Bool × Bool)

/-- Joint response law of the independent assignment and outcome components. -/
def jointResponseMass
    (model : MarkovianAssignmentOutcomeModel) :
    Bool × (Bool × Bool) → ℚ :=
  productResponseMass model.assignmentLaw.mass model.outcomeLaw.mass

/-- Benefit probability evaluated in the full joint Markovian response law. -/
def markovianBenefitMass
    (jointMass : Bool × (Bool × Bool) → ℚ) : ℚ :=
  ∑ assignment, jointMass (assignment, (false, true))

/-- Marginalizing the independent normalized assignment component leaves the
outcome-mechanism benefit mass unchanged. -/
theorem markovianBenefitMass_product
    (assignmentLaw : FiniteResponseLaw Bool)
    (outcomeMass : Bool × Bool → ℚ) :
    markovianBenefitMass
        (productResponseMass assignmentLaw.mass outcomeMass) =
      benefitResponseMass outcomeMass := by
  unfold markovianBenefitMass productResponseMass benefitResponseMass
  rw [Finset.sum_mul, assignmentLaw.total, one_mul]

/-- Explicit four-cell outcome-response law with nominated control success,
treated success, and benefit probability. -/
def benefitResponseVector
    (controlSuccess treatedSuccess benefit : ℚ) :
    Bool × Bool → ℚ
  | (false, false) => 1 - controlSuccess - benefit
  | (false, true) => benefit
  | (true, false) => controlSuccess - treatedSuccess + benefit
  | (true, true) => treatedSuccess - benefit

/-- Every target in the Boolean benefit Frechet interval defines a normalized
nonnegative outcome-response law. -/
def benefitResponseLaw
    (controlSuccess treatedSuccess benefit : ℚ)
    (lower : max 0 (treatedSuccess - controlSuccess) ≤ benefit)
    (upper : benefit ≤ min treatedSuccess (1 - controlSuccess)) :
    FiniteResponseLaw (Bool × Bool) := by
  have benefit_nonnegative : 0 ≤ benefit :=
    (le_max_left 0 (treatedSuccess - controlSuccess)).trans lower
  have difference_lower : treatedSuccess - controlSuccess ≤ benefit :=
    (le_max_right 0 (treatedSuccess - controlSuccess)).trans lower
  have benefit_le_treated : benefit ≤ treatedSuccess :=
    upper.trans (min_le_left treatedSuccess (1 - controlSuccess))
  have benefit_le_control_complement : benefit ≤ 1 - controlSuccess :=
    upper.trans (min_le_right treatedSuccess (1 - controlSuccess))
  refine
    { mass := benefitResponseVector controlSuccess treatedSuccess benefit
      nonnegative := ?_
      total := ?_ }
  · intro response
    rcases response with ⟨control, treated⟩
    cases control <;> cases treated <;>
      simp [benefitResponseVector] <;> linarith
  · simp [benefitResponseVector]

@[simp] theorem benefitResponseLaw_controlMarginal
    (controlSuccess treatedSuccess benefit : ℚ)
    (lower : max 0 (treatedSuccess - controlSuccess) ≤ benefit)
    (upper : benefit ≤ min treatedSuccess (1 - controlSuccess)) :
    controlSuccessMarginal
        (benefitResponseLaw
          controlSuccess treatedSuccess benefit lower upper).mass =
      controlSuccess := by
  simp [benefitResponseLaw, controlSuccessMarginal, benefitResponseVector]

@[simp] theorem benefitResponseLaw_treatmentMarginal
    (controlSuccess treatedSuccess benefit : ℚ)
    (lower : max 0 (treatedSuccess - controlSuccess) ≤ benefit)
    (upper : benefit ≤ min treatedSuccess (1 - controlSuccess)) :
    treatmentSuccessMarginal
        (benefitResponseLaw
          controlSuccess treatedSuccess benefit lower upper).mass =
      treatedSuccess := by
  simp [benefitResponseLaw, treatmentSuccessMarginal, benefitResponseVector]

@[simp] theorem benefitResponseLaw_benefit
    (controlSuccess treatedSuccess benefit : ℚ)
    (lower : max 0 (treatedSuccess - controlSuccess) ≤ benefit)
    (upper : benefit ≤ min treatedSuccess (1 - controlSuccess)) :
    benefitResponseMass
        (benefitResponseLaw
          controlSuccess treatedSuccess benefit lower upper).mass =
      benefit := by
  rfl

/-- Standard Markovian independence between assignment disturbance and the
outcome mechanism does not tighten the Boolean benefit interval. Every target
in the ordinary Frechet interval is realized by a product assignment-outcome
response law, and every such model obeys those bounds. -/
theorem markovian_benefit_target_feasible_iff
    (controlSuccess treatedSuccess benefit : ℚ) :
    (max 0 (treatedSuccess - controlSuccess) ≤ benefit ∧
        benefit ≤ min treatedSuccess (1 - controlSuccess)) ↔
      ∃ model : MarkovianAssignmentOutcomeModel,
        controlSuccessMarginal model.outcomeLaw.mass = controlSuccess ∧
          treatmentSuccessMarginal model.outcomeLaw.mass = treatedSuccess ∧
          markovianBenefitMass (jointResponseMass model) = benefit := by
  constructor
  · rintro ⟨lower, upper⟩
    let assignmentLaw : FiniteResponseLaw Bool := boolPointLaw false
    let outcomeLaw : FiniteResponseLaw (Bool × Bool) :=
      benefitResponseLaw
        controlSuccess treatedSuccess benefit lower upper
    refine
      ⟨{ assignmentLaw := assignmentLaw, outcomeLaw := outcomeLaw },
        ?_, ?_, ?_⟩
    · exact benefitResponseLaw_controlMarginal
        controlSuccess treatedSuccess benefit lower upper
    · exact benefitResponseLaw_treatmentMarginal
        controlSuccess treatedSuccess benefit lower upper
    · rw [jointResponseMass, markovianBenefitMass_product]
      exact benefitResponseLaw_benefit
        controlSuccess treatedSuccess benefit lower upper
  · rintro ⟨model, control_eq, treated_eq, benefit_eq⟩
    have benefit_outcome_eq :
        benefitResponseMass model.outcomeLaw.mass = benefit := by
      rw [jointResponseMass, markovianBenefitMass_product] at benefit_eq
      exact benefit_eq
    have m00_nonnegative := model.outcomeLaw.nonnegative (false, false)
    have m01_nonnegative := model.outcomeLaw.nonnegative (false, true)
    have m10_nonnegative := model.outcomeLaw.nonnegative (true, false)
    have m11_nonnegative := model.outcomeLaw.nonnegative (true, true)
    have total_four :
        model.outcomeLaw.mass (false, false) +
            model.outcomeLaw.mass (false, true) +
            model.outcomeLaw.mass (true, false) +
            model.outcomeLaw.mass (true, true) = 1 := by
      simpa [Fintype.sum_prod_type, Fintype.sum_bool] using
        model.outcomeLaw.total
    constructor
    · rw [max_le_iff]
      constructor
      · unfold benefitResponseMass at benefit_outcome_eq
        linarith
      · unfold controlSuccessMarginal at control_eq
        unfold treatmentSuccessMarginal at treated_eq
        unfold benefitResponseMass at benefit_outcome_eq
        linarith
    · rw [le_min_iff]
      constructor
      · unfold treatmentSuccessMarginal at treated_eq
        unfold benefitResponseMass at benefit_outcome_eq
        linarith
      · unfold controlSuccessMarginal at control_eq
        unfold benefitResponseMass at benefit_outcome_eq
        linarith

/-- Concrete failure of point identification. Two Markovian
assignment-outcome models have the same control and treated success marginals
one half, while their benefit probabilities are zero and one half. -/
theorem markovian_assignment_noise_does_not_point_identify_benefit :
    ∃ first second : MarkovianAssignmentOutcomeModel,
      controlSuccessMarginal first.outcomeLaw.mass = (1 / 2 : ℚ) ∧
        treatmentSuccessMarginal first.outcomeLaw.mass = (1 / 2 : ℚ) ∧
        markovianBenefitMass (jointResponseMass first) = 0 ∧
        controlSuccessMarginal second.outcomeLaw.mass = (1 / 2 : ℚ) ∧
        treatmentSuccessMarginal second.outcomeLaw.mass = (1 / 2 : ℚ) ∧
        markovianBenefitMass (jointResponseMass second) = (1 / 2 : ℚ) := by
  have first_exists :=
    (markovian_benefit_target_feasible_iff
      (1 / 2 : ℚ) (1 / 2 : ℚ) 0).mp (by norm_num)
  have second_exists :=
    (markovian_benefit_target_feasible_iff
      (1 / 2 : ℚ) (1 / 2 : ℚ) (1 / 2 : ℚ)).mp (by norm_num)
  rcases first_exists with ⟨first, first_control, first_treated, first_benefit⟩
  rcases second_exists with
    ⟨second, second_control, second_treated, second_benefit⟩
  exact
    ⟨first, second, first_control, first_treated, first_benefit,
      second_control, second_treated, second_benefit⟩

/-- Factorizing the two potential-outcome coordinates inside the outcome
response law is stronger than standard Markovian assignment independence. Under
this extra cross-world restriction, benefit is point identified as
`(1 - p0) * p1`. -/
theorem response_coordinate_factorization_point_identifies_benefit
    (outcomeMass : Bool × Bool → ℚ)
    (factorized : IsMarkovianTwoComponentLaw outcomeMass)
    (controlSuccess treatedSuccess : ℚ)
    (control_eq : controlSuccessMarginal outcomeMass = controlSuccess)
    (treated_eq : treatmentSuccessMarginal outcomeMass = treatedSuccess) :
    benefitResponseMass outcomeMass =
      (1 - controlSuccess) * treatedSuccess := by
  rcases factorized with ⟨controlLaw, treatedLaw, outcome_eq⟩
  subst outcomeMass
  have control_total :
      controlLaw.mass false + controlLaw.mass true = 1 := by
    simpa [Fintype.sum_bool] using controlLaw.total
  have treated_total :
      treatedLaw.mass false + treatedLaw.mass true = 1 := by
    simpa [Fintype.sum_bool] using treatedLaw.total
  have control_formula :
      controlSuccessMarginal
          (productResponseMass controlLaw.mass treatedLaw.mass) =
        controlLaw.mass true := by
    unfold controlSuccessMarginal productResponseMass
    calc
      controlLaw.mass true * treatedLaw.mass false +
          controlLaw.mass true * treatedLaw.mass true =
        controlLaw.mass true *
          (treatedLaw.mass false + treatedLaw.mass true) := by ring
      _ = controlLaw.mass true := by rw [treated_total, mul_one]
  have treated_formula :
      treatmentSuccessMarginal
          (productResponseMass controlLaw.mass treatedLaw.mass) =
        treatedLaw.mass true := by
    unfold treatmentSuccessMarginal productResponseMass
    calc
      controlLaw.mass false * treatedLaw.mass true +
          controlLaw.mass true * treatedLaw.mass true =
        (controlLaw.mass false + controlLaw.mass true) *
          treatedLaw.mass true := by ring
      _ = treatedLaw.mass true := by rw [control_total, one_mul]
  rw [control_formula] at control_eq
  rw [treated_formula] at treated_eq
  unfold benefitResponseMass productResponseMass
  have control_false :
      controlLaw.mass false = 1 - controlSuccess := by
    linarith [control_total, control_eq]
  rw [control_false, treated_eq]

#print axioms markovianBenefitMass_product
#print axioms markovian_benefit_target_feasible_iff
#print axioms markovian_assignment_noise_does_not_point_identify_benefit
#print axioms response_coordinate_factorization_point_identifies_benefit

end D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianBenefitIdentificationBoundary

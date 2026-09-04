/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/MarkovianJointMechanismBenefitSharpBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/MarkovianJointMechanismBenefitSharpBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two mechanism-level benefit events have a sharp Frechet coupling interval, while Markovian independence across mechanisms collapses the joint benefit query to the product of its benefit marginals. -/

import D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianBenefitIdentificationBoundary
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04):
   * `MarkovianBenefitIdentificationBoundary` proves that standard independence
     between treatment assignment and one outcome mechanism leaves the
     within-mechanism Boolean benefit query at its full Frechet interval.
   * `MarkovianResponseLawFactorization` proves that independent exogenous
     components induce product response laws and that deterministic
     componentwise pushforwards preserve that factorization.
   * Repository searches found no theorem comparing an unrestricted coupling of
     two mechanism-level benefit events with the product restriction induced by
     independent Markovian outcome mechanisms.
   * The result below keeps each mechanism's internal potential-outcome
     coupling arbitrary. Independence is imposed only between the two complete
     mechanism response laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianJointMechanismBenefitSharpBounds

open scoped BigOperators
open D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianBenefitIdentificationBoundary

/-- Marginal probability that the first mechanism benefits. -/
def firstBenefitIndicatorMarginal (mass : Bool × Bool → ℚ) : ℚ :=
  mass (true, false) + mass (true, true)

/-- Marginal probability that the second mechanism benefits. -/
def secondBenefitIndicatorMarginal (mass : Bool × Bool → ℚ) : ℚ :=
  mass (false, true) + mass (true, true)

/-- Probability that both mechanism-level benefit indicators are true. -/
def jointBenefitIndicatorMass (mass : Bool × Bool → ℚ) : ℚ :=
  mass (true, true)

/-- Explicit coupling of two Boolean mechanism-level benefit indicators with
nominated marginals and nominated joint benefit mass. -/
def benefitIndicatorCouplingVector
    (firstBenefit secondBenefit jointBenefit : ℚ) :
    Bool × Bool → ℚ
  | (false, false) => 1 - firstBenefit - secondBenefit + jointBenefit
  | (false, true) => secondBenefit - jointBenefit
  | (true, false) => firstBenefit - jointBenefit
  | (true, true) => jointBenefit

/-- Every target in the two-event Frechet interval defines a normalized
nonnegative coupling law for the two mechanism-level benefit indicators. -/
def benefitIndicatorCouplingLaw
    (firstBenefit secondBenefit jointBenefit : ℚ)
    (lower :
      max 0 (firstBenefit + secondBenefit - 1) ≤ jointBenefit)
    (upper : jointBenefit ≤ min firstBenefit secondBenefit) :
    FiniteResponseLaw (Bool × Bool) := by
  have joint_nonnegative : 0 ≤ jointBenefit :=
    (le_max_left 0 (firstBenefit + secondBenefit - 1)).trans lower
  have frechet_lower :
      firstBenefit + secondBenefit - 1 ≤ jointBenefit :=
    (le_max_right 0 (firstBenefit + secondBenefit - 1)).trans lower
  have joint_le_first : jointBenefit ≤ firstBenefit :=
    upper.trans (min_le_left firstBenefit secondBenefit)
  have joint_le_second : jointBenefit ≤ secondBenefit :=
    upper.trans (min_le_right firstBenefit secondBenefit)
  refine
    { mass :=
        benefitIndicatorCouplingVector
          firstBenefit secondBenefit jointBenefit
      nonnegative := ?_
      total := ?_ }
  · intro response
    rcases response with ⟨first, second⟩
    cases first <;> cases second <;>
      simp [benefitIndicatorCouplingVector] <;> linarith
  · simp [benefitIndicatorCouplingVector]

@[simp] theorem benefitIndicatorCouplingLaw_firstMarginal
    (firstBenefit secondBenefit jointBenefit : ℚ)
    (lower :
      max 0 (firstBenefit + secondBenefit - 1) ≤ jointBenefit)
    (upper : jointBenefit ≤ min firstBenefit secondBenefit) :
    firstBenefitIndicatorMarginal
        (benefitIndicatorCouplingLaw
          firstBenefit secondBenefit jointBenefit lower upper).mass =
      firstBenefit := by
  simp [benefitIndicatorCouplingLaw, firstBenefitIndicatorMarginal,
    benefitIndicatorCouplingVector]

@[simp] theorem benefitIndicatorCouplingLaw_secondMarginal
    (firstBenefit secondBenefit jointBenefit : ℚ)
    (lower :
      max 0 (firstBenefit + secondBenefit - 1) ≤ jointBenefit)
    (upper : jointBenefit ≤ min firstBenefit secondBenefit) :
    secondBenefitIndicatorMarginal
        (benefitIndicatorCouplingLaw
          firstBenefit secondBenefit jointBenefit lower upper).mass =
      secondBenefit := by
  simp [benefitIndicatorCouplingLaw, secondBenefitIndicatorMarginal,
    benefitIndicatorCouplingVector]

@[simp] theorem benefitIndicatorCouplingLaw_jointMass
    (firstBenefit secondBenefit jointBenefit : ℚ)
    (lower :
      max 0 (firstBenefit + secondBenefit - 1) ≤ jointBenefit)
    (upper : jointBenefit ≤ min firstBenefit secondBenefit) :
    jointBenefitIndicatorMass
        (benefitIndicatorCouplingLaw
          firstBenefit secondBenefit jointBenefit lower upper).mass =
      jointBenefit := by
  rfl

/-- The unrestricted coupling identified set for two mechanism-level benefit
events is exactly the Frechet interval. Necessity uses cell nonnegativity and
normalization. Sufficiency uses the explicit four-cell coupling law. -/
theorem unrestricted_joint_benefit_target_feasible_iff
    (firstBenefit secondBenefit jointBenefit : ℚ) :
    (max 0 (firstBenefit + secondBenefit - 1) ≤ jointBenefit ∧
        jointBenefit ≤ min firstBenefit secondBenefit) ↔
      ∃ law : FiniteResponseLaw (Bool × Bool),
        firstBenefitIndicatorMarginal law.mass = firstBenefit ∧
          secondBenefitIndicatorMarginal law.mass = secondBenefit ∧
          jointBenefitIndicatorMass law.mass = jointBenefit := by
  constructor
  · rintro ⟨lower, upper⟩
    refine
      ⟨benefitIndicatorCouplingLaw
          firstBenefit secondBenefit jointBenefit lower upper,
        ?_, ?_, ?_⟩
    · exact benefitIndicatorCouplingLaw_firstMarginal
        firstBenefit secondBenefit jointBenefit lower upper
    · exact benefitIndicatorCouplingLaw_secondMarginal
        firstBenefit secondBenefit jointBenefit lower upper
    · exact benefitIndicatorCouplingLaw_jointMass
        firstBenefit secondBenefit jointBenefit lower upper
  · rintro ⟨law, first_eq, second_eq, joint_eq⟩
    have total_four :
        law.mass (false, false) + law.mass (false, true) +
            law.mass (true, false) + law.mass (true, true) = 1 := by
      simpa [Fintype.sum_prod_type, Fintype.sum_bool] using law.total
    have m00_nonnegative := law.nonnegative (false, false)
    have m01_nonnegative := law.nonnegative (false, true)
    have m10_nonnegative := law.nonnegative (true, false)
    have m11_nonnegative := law.nonnegative (true, true)
    constructor
    · rw [max_le_iff]
      constructor
      · unfold jointBenefitIndicatorMass at joint_eq
        linarith
      · unfold firstBenefitIndicatorMarginal at first_eq
        unfold secondBenefitIndicatorMarginal at second_eq
        unfold jointBenefitIndicatorMass at joint_eq
        linarith
    · rw [le_min_iff]
      constructor
      · unfold firstBenefitIndicatorMarginal at first_eq
        unfold jointBenefitIndicatorMass at joint_eq
        linarith
      · unfold secondBenefitIndicatorMarginal at second_eq
        unfold jointBenefitIndicatorMass at joint_eq
        linarith

/-- A full outcome mechanism benefits exactly on response pair `(false,true)`. -/
def benefitStatus : Bool × Bool → Bool
  | (false, true) => true
  | _ => false

/-- Push one complete outcome-mechanism response law to its Boolean benefit
status. Dependence between its two potential-outcome coordinates remains
unrestricted before this deterministic projection. -/
noncomputable def benefitStatusLaw
    (law : FiniteResponseLaw (Bool × Bool)) :
    FiniteResponseLaw Bool :=
  pushforwardResponseLaw law benefitStatus

@[simp] theorem benefitStatusLaw_true_mass
    (law : FiniteResponseLaw (Bool × Bool)) :
    (benefitStatusLaw law).mass true = benefitResponseMass law.mass := by
  classical
  simp [benefitStatusLaw, pushforwardResponseLaw,
    pushforwardSignatureMass, benefitStatus, benefitResponseMass,
    Fintype.sum_prod_type, Fintype.sum_bool]

/-- Two complete outcome mechanisms with independent exogenous components.
Each component law may contain arbitrary dependence between its own control and
treated potential-outcome coordinates. -/
structure MarkovianJointMechanismModel where
  firstLaw : FiniteResponseLaw (Bool × Bool)
  secondLaw : FiniteResponseLaw (Bool × Bool)

/-- Product response law of the two independent outcome mechanisms. -/
def markovianJointResponseMass
    (model : MarkovianJointMechanismModel) :
    (Bool × Bool) × (Bool × Bool) → ℚ :=
  productResponseMass model.firstLaw.mass model.secondLaw.mass

/-- Joint probability that both complete outcome mechanisms benefit. -/
def jointMechanismBenefitMass
    (jointMass : (Bool × Bool) × (Bool × Bool) → ℚ) : ℚ :=
  jointMass ((false, true), (false, true))

/-- Projecting two independent complete mechanism responses to their Boolean
benefit indicators preserves product factorization. -/
theorem markovian_benefit_status_pushforward_factorizes
    (model : MarkovianJointMechanismModel) :
    pushforwardSignatureMass
        (markovianJointResponseMass model)
        (fun response =>
          (benefitStatus response.1, benefitStatus response.2)) =
      productResponseMass
        (benefitStatusLaw model.firstLaw).mass
        (benefitStatusLaw model.secondLaw).mass := by
  simpa [markovianJointResponseMass, benefitStatusLaw,
    pushforwardResponseLaw] using
    (product_pushforward_factorizes
      model.firstLaw.mass model.secondLaw.mass benefitStatus benefitStatus)

/-- Under a product response law, simultaneous benefit equals the product of
the two mechanism-level benefit probabilities. -/
theorem jointMechanismBenefitMass_product
    (firstMass secondMass : Bool × Bool → ℚ) :
    jointMechanismBenefitMass
        (productResponseMass firstMass secondMass) =
      benefitResponseMass firstMass * benefitResponseMass secondMass := by
  rfl

/-- Every Markovian two-mechanism model has joint benefit probability equal to
the product of its two marginal mechanism benefit probabilities. -/
theorem markovianJointBenefit_eq_product
    (model : MarkovianJointMechanismModel) :
    jointMechanismBenefitMass (markovianJointResponseMass model) =
      benefitResponseMass model.firstLaw.mass *
        benefitResponseMass model.secondLaw.mass := by
  exact jointMechanismBenefitMass_product
    model.firstLaw.mass model.secondLaw.mass

/-- A complete outcome-mechanism response law whose benefit probability is the
nominated value. Its within-mechanism coupling is chosen explicitly only to
construct an attaining witness. -/
def mechanismBenefitLaw
    (benefit : ℚ)
    (nonnegative : 0 ≤ benefit)
    (atMostOne : benefit ≤ 1) :
    FiniteResponseLaw (Bool × Bool) :=
  benefitResponseLaw 0 benefit benefit
    (by
      rw [sub_zero, max_eq_right nonnegative])
    (by
      rw [le_min_iff]
      exact ⟨le_rfl, by simpa using atMostOne⟩)

@[simp] theorem mechanismBenefitLaw_benefit
    (benefit : ℚ)
    (nonnegative : 0 ≤ benefit)
    (atMostOne : benefit ≤ 1) :
    benefitResponseMass
        (mechanismBenefitLaw benefit nonnegative atMostOne).mass =
      benefit := by
  simp [mechanismBenefitLaw]

/-- Markovian independence across two complete outcome mechanisms collapses
the joint-benefit identified set to the sharp singleton containing the product
of the two benefit marginals. -/
theorem markovian_joint_benefit_sharp_singleton_iff
    (firstBenefit secondBenefit target : ℚ)
    (first_nonnegative : 0 ≤ firstBenefit)
    (first_at_most_one : firstBenefit ≤ 1)
    (second_nonnegative : 0 ≤ secondBenefit)
    (second_at_most_one : secondBenefit ≤ 1) :
    target = firstBenefit * secondBenefit ↔
      ∃ model : MarkovianJointMechanismModel,
        benefitResponseMass model.firstLaw.mass = firstBenefit ∧
          benefitResponseMass model.secondLaw.mass = secondBenefit ∧
          jointMechanismBenefitMass
              (markovianJointResponseMass model) = target := by
  constructor
  · intro target_eq
    let firstLaw :=
      mechanismBenefitLaw
        firstBenefit first_nonnegative first_at_most_one
    let secondLaw :=
      mechanismBenefitLaw
        secondBenefit second_nonnegative second_at_most_one
    refine
      ⟨{ firstLaw := firstLaw, secondLaw := secondLaw },
        ?_, ?_, ?_⟩
    · simpa [firstLaw] using
        mechanismBenefitLaw_benefit
          firstBenefit first_nonnegative first_at_most_one
    · simpa [secondLaw] using
        mechanismBenefitLaw_benefit
          secondBenefit second_nonnegative second_at_most_one
    · calc
        jointMechanismBenefitMass
            (markovianJointResponseMass
              { firstLaw := firstLaw, secondLaw := secondLaw }) =
          benefitResponseMass firstLaw.mass *
            benefitResponseMass secondLaw.mass :=
              markovianJointBenefit_eq_product
                { firstLaw := firstLaw, secondLaw := secondLaw }
        _ = firstBenefit * secondBenefit := by
          rw [show benefitResponseMass firstLaw.mass = firstBenefit by
                simpa [firstLaw] using
                  mechanismBenefitLaw_benefit
                    firstBenefit first_nonnegative first_at_most_one,
              show benefitResponseMass secondLaw.mass = secondBenefit by
                simpa [secondLaw] using
                  mechanismBenefitLaw_benefit
                    secondBenefit second_nonnegative second_at_most_one]
        _ = target := target_eq.symm
  · rintro ⟨model, first_eq, second_eq, target_eq⟩
    calc
      target =
          jointMechanismBenefitMass
            (markovianJointResponseMass model) := target_eq.symm
      _ = benefitResponseMass model.firstLaw.mass *
          benefitResponseMass model.secondLaw.mass :=
            markovianJointBenefit_eq_product model
      _ = firstBenefit * secondBenefit := by rw [first_eq, second_eq]

/-- With both marginal mechanism benefit probabilities equal to one half, the
unrestricted coupling identified set is the complete interval `[0,1/2]`. -/
theorem half_unrestricted_joint_benefit_target_feasible_iff
    (target : ℚ) :
    (0 ≤ target ∧ target ≤ 1 / 2) ↔
      ∃ law : FiniteResponseLaw (Bool × Bool),
        firstBenefitIndicatorMarginal law.mass = 1 / 2 ∧
          secondBenefitIndicatorMarginal law.mass = 1 / 2 ∧
          jointBenefitIndicatorMass law.mass = target := by
  simpa using
    (unrestricted_joint_benefit_target_feasible_iff
      (1 / 2 : ℚ) (1 / 2 : ℚ) target)

/-- With both marginal mechanism benefit probabilities equal to one half,
Markovian independence point identifies simultaneous benefit at one quarter. -/
theorem half_markovian_joint_benefit_target_feasible_iff
    (target : ℚ) :
    target = 1 / 4 ↔
      ∃ model : MarkovianJointMechanismModel,
        benefitResponseMass model.firstLaw.mass = 1 / 2 ∧
          benefitResponseMass model.secondLaw.mass = 1 / 2 ∧
          jointMechanismBenefitMass
              (markovianJointResponseMass model) = target := by
  simpa using
    (markovian_joint_benefit_sharp_singleton_iff
      (1 / 2 : ℚ) (1 / 2 : ℚ) target
      (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The half-marginal example exhibits strict tightening. Zero simultaneous
benefit is attainable under unrestricted cross-mechanism coupling, while every
Markovian two-mechanism model with the same benefit marginals has simultaneous
benefit one quarter. -/
theorem half_joint_benefit_strict_tightening :
    (∃ law : FiniteResponseLaw (Bool × Bool),
        firstBenefitIndicatorMarginal law.mass = 1 / 2 ∧
          secondBenefitIndicatorMarginal law.mass = 1 / 2 ∧
          jointBenefitIndicatorMass law.mass = 0) ∧
      (∀ model : MarkovianJointMechanismModel,
        benefitResponseMass model.firstLaw.mass = 1 / 2 →
        benefitResponseMass model.secondLaw.mass = 1 / 2 →
        jointMechanismBenefitMass
            (markovianJointResponseMass model) = 1 / 4) := by
  constructor
  · exact
      (half_unrestricted_joint_benefit_target_feasible_iff 0).mp
        (by norm_num)
  · intro model first_eq second_eq
    rw [markovianJointBenefit_eq_product, first_eq, second_eq]
    norm_num

#print axioms unrestricted_joint_benefit_target_feasible_iff
#print axioms markovian_benefit_status_pushforward_factorizes
#print axioms markovian_joint_benefit_sharp_singleton_iff
#print axioms half_joint_benefit_strict_tightening

end D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianJointMechanismBenefitSharpBounds

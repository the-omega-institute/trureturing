/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/BooleanMarkovianResponseLawCharacterization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/BooleanMarkovianResponseLawCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A normalized nonnegative Boolean two-component response law factorizes exactly when its two-by-two determinant vanishes; for benefit responses the determinant residual is the gap from the product-formula identification boundary. -/

import D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianBenefitIdentificationBoundary

/- Library-search audit trail (2026-09-04):
   * `MarkovianResponseLawFactorization` proves determinant zero is necessary
     for product response laws and gives a nonconvex midpoint witness.
   * `MarkovianBenefitIdentificationBoundary` separates ordinary Markovian
     assignment independence from the stronger independence of the two
     potential-outcome coordinates.
   * Repository searches found no converse showing that determinant zero is
     sufficient for a normalized nonnegative Boolean response law, nor the
     exact determinant-residual identity for the complete benefit witness
     family.
   * This module proves both. The constructive factorization uses the two
     coordinate marginals, and the benefit residual reduces to the affine gap
     `(1 - p0) * p1 - q`.
   * No multivalued rank-one-minor characterization is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.BooleanMarkovianResponseLawCharacterization

open scoped BigOperators
open D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.Causal.PartialIdentification.MarkovianBenefitIdentificationBoundary

/-- A normalized Boolean joint response law has exactly four cells. -/
theorem booleanJointLaw_total_four
    (jointLaw : FiniteResponseLaw (Bool × Bool)) :
    jointLaw.mass (false, false) +
        jointLaw.mass (false, true) +
        jointLaw.mass (true, false) +
        jointLaw.mass (true, true) = 1 := by
  simpa [Fintype.sum_prod_type, Fintype.sum_bool] using jointLaw.total

/-- The first-coordinate marginal of a normalized Boolean joint response law. -/
def booleanLeftMarginalLaw
    (jointLaw : FiniteResponseLaw (Bool × Bool)) :
    FiniteResponseLaw Bool where
  mass := leftResponseMarginal jointLaw.mass
  nonnegative := by
    intro left
    unfold leftResponseMarginal
    apply Finset.sum_nonneg
    intro right _
    exact jointLaw.nonnegative (left, right)
  total := by
    have total_four := booleanJointLaw_total_four jointLaw
    unfold leftResponseMarginal
    simp only [Fintype.sum_bool]
    linarith

/-- The second-coordinate marginal of a normalized Boolean joint response law. -/
def booleanRightMarginalLaw
    (jointLaw : FiniteResponseLaw (Bool × Bool)) :
    FiniteResponseLaw Bool where
  mass := rightResponseMarginal jointLaw.mass
  nonnegative := by
    intro right
    unfold rightResponseMarginal
    apply Finset.sum_nonneg
    intro left _
    exact jointLaw.nonnegative (left, right)
  total := by
    have total_four := booleanJointLaw_total_four jointLaw
    unfold rightResponseMarginal
    simp only [Fintype.sum_bool]
    linarith

/-- A normalized nonnegative Boolean two-component response law factorizes if
and only if its two-by-two determinant vanishes. The reverse direction is
constructive: the two factor laws are the coordinate marginals. -/
theorem boolean_markovian_iff_determinant_zero
    (jointLaw : FiniteResponseLaw (Bool × Bool)) :
    IsMarkovianTwoComponentLaw jointLaw.mass ↔
      jointLaw.mass (true, true) * jointLaw.mass (false, false) =
        jointLaw.mass (true, false) * jointLaw.mass (false, true) := by
  constructor
  · intro markovian
    exact markovianTwoComponent_determinant_zero jointLaw.mass markovian
  · intro determinant
    refine
      ⟨booleanLeftMarginalLaw jointLaw,
        booleanRightMarginalLaw jointLaw, ?_⟩
    funext response
    rcases response with ⟨left, right⟩
    have total_four := booleanJointLaw_total_four jointLaw
    cases left <;> cases right <;>
      simp [booleanLeftMarginalLaw, booleanRightMarginalLaw,
        leftResponseMarginal, rightResponseMarginal,
        productResponseMass, Fintype.sum_bool] <;>
      nlinarith

/-- Signed determinant residual of a Boolean two-component response mass. -/
def booleanResponseDeterminant
    (mass : Bool × Bool → ℚ) : ℚ :=
  mass (true, true) * mass (false, false) -
    mass (true, false) * mass (false, true)

/-- Determinant-residual form of the complete Boolean factorization criterion. -/
theorem boolean_markovian_iff_responseDeterminant_zero
    (jointLaw : FiniteResponseLaw (Bool × Bool)) :
    IsMarkovianTwoComponentLaw jointLaw.mass ↔
      booleanResponseDeterminant jointLaw.mass = 0 := by
  constructor
  · intro factorized
    unfold booleanResponseDeterminant
    have determinant :=
      markovianTwoComponent_determinant_zero jointLaw.mass factorized
    linarith
  · intro determinant
    apply (boolean_markovian_iff_determinant_zero jointLaw).2
    unfold booleanResponseDeterminant at determinant
    linarith

/-- For the complete Boolean benefit witness family, the determinant residual
is exactly the gap between the product-formula target and the nominated benefit
mass. -/
theorem benefitResponseVector_determinant_gap
    (controlSuccess treatedSuccess benefit : ℚ) :
    booleanResponseDeterminant
        (benefitResponseVector
          controlSuccess treatedSuccess benefit) =
      (1 - controlSuccess) * treatedSuccess - benefit := by
  unfold booleanResponseDeterminant
  simp [benefitResponseVector]
  ring

/-- The complete Boolean benefit witness has determinant zero exactly at the
product-formula value. -/
theorem benefitResponseVector_determinant_zero_iff
    (controlSuccess treatedSuccess benefit : ℚ) :
    booleanResponseDeterminant
        (benefitResponseVector
          controlSuccess treatedSuccess benefit) = 0 ↔
      benefit = (1 - controlSuccess) * treatedSuccess := by
  rw [benefitResponseVector_determinant_gap]
  constructor <;> intro gap <;> linarith

/-- Vanishing determinant point-identifies benefit from the two intervention
marginals. -/
theorem determinant_zero_point_identifies_benefit
    (outcomeLaw : FiniteResponseLaw (Bool × Bool))
    (controlSuccess treatedSuccess : ℚ)
    (control_eq :
      controlSuccessMarginal outcomeLaw.mass = controlSuccess)
    (treated_eq :
      treatmentSuccessMarginal outcomeLaw.mass = treatedSuccess)
    (determinant :
      booleanResponseDeterminant outcomeLaw.mass = 0) :
    benefitResponseMass outcomeLaw.mass =
      (1 - controlSuccess) * treatedSuccess := by
  exact response_coordinate_factorization_point_identifies_benefit
    outcomeLaw.mass
    ((boolean_markovian_iff_responseDeterminant_zero outcomeLaw).2
      determinant)
    controlSuccess treatedSuccess control_eq treated_eq

/-- Inside the explicit sharp Frechet witness family, response-coordinate
factorization holds at exactly one target, namely `(1 - p0) * p1`. -/
theorem benefitResponseLaw_factorized_iff
    (controlSuccess treatedSuccess benefit : ℚ)
    (lower : max 0 (treatedSuccess - controlSuccess) ≤ benefit)
    (upper : benefit ≤ min treatedSuccess (1 - controlSuccess)) :
    IsMarkovianTwoComponentLaw
        (benefitResponseLaw
          controlSuccess treatedSuccess benefit lower upper).mass ↔
      benefit = (1 - controlSuccess) * treatedSuccess := by
  constructor
  · intro factorized
    have determinant :
        booleanResponseDeterminant
          (benefitResponseLaw
            controlSuccess treatedSuccess benefit lower upper).mass = 0 :=
      (boolean_markovian_iff_responseDeterminant_zero
        (benefitResponseLaw
          controlSuccess treatedSuccess benefit lower upper)).1
        factorized
    change
      booleanResponseDeterminant
          (benefitResponseVector
            controlSuccess treatedSuccess benefit) = 0 at determinant
    exact
      (benefitResponseVector_determinant_zero_iff
        controlSuccess treatedSuccess benefit).1 determinant
  · intro product_formula
    apply
      (boolean_markovian_iff_responseDeterminant_zero
        (benefitResponseLaw
          controlSuccess treatedSuccess benefit lower upper)).2
    change
      booleanResponseDeterminant
          (benefitResponseVector
            controlSuccess treatedSuccess benefit) = 0
    exact
      (benefitResponseVector_determinant_zero_iff
        controlSuccess treatedSuccess benefit).2 product_formula

#print axioms boolean_markovian_iff_determinant_zero
#print axioms boolean_markovian_iff_responseDeterminant_zero
#print axioms benefitResponseVector_determinant_gap
#print axioms determinant_zero_point_identifies_benefit
#print axioms benefitResponseLaw_factorized_iff

end D5.S3.ConceptDynamics.Causal.PartialIdentification.BooleanMarkovianResponseLawCharacterization

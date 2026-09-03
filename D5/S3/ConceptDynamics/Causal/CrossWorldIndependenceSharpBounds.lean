/- GID: D5/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/CrossWorldIndependenceSharpBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A polynomial cross-world independence restriction collapses a two-event joint query to a sharp singleton and is globally nonconvex. -/

import D5.S3.ConceptDynamics.Causal.FiniteEventCouplingSharpBounds
import D5.S3.ConceptDynamics.Causal.NonconvexSharpIdentification
import Mathlib.Tactic.Nlinarith

/- Library-search audit trail (2026-09-03):
   * `FiniteEventCouplingSharpBounds` characterizes the unrestricted two-event
     coupling interval and supplies an explicit four-cell witness.
   * `NonconvexSharpIdentification` separates exact endpoints from full range
     sharpness when convex interpolation is unavailable.
   * Repository searches found no causal truth source treating a polynomial
     cross-world factorization equality or formally showing that the resulting
     family is not closed under mixtures. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.CrossWorldIndependenceSharpBounds

open D5.S3.ConceptDynamics.Causal.FiniteEventCouplingSharpBounds

/-- Vanishing of the two-by-two determinant is the polynomial factorization
condition for two Boolean event indicators. -/
def IndependentDeterminant (mass : Bool × Bool -> Real) : Prop :=
  mass (true, true) * mass (false, false) =
    mass (true, false) * mass (false, true)

/-- A normalized event coupling with fixed marginals and the polynomial
cross-world independence restriction. -/
def IsIndependentEventCoupling
    (mass : Bool × Bool -> Real)
    (leftMarginal rightMarginal : Real) : Prop :=
  IsEventCoupling mass leftMarginal rightMarginal /\
    IndependentDeterminant mass

/-- The cross-world joint event query. -/
def jointEventMass (mass : Bool × Bool -> Real) : Real :=
  mass (true, true)

/-- The determinant equation and the marginal rows force the joint event mass
to equal the product of the marginals. -/
theorem independent_joint_event_eq_product
    (mass : Bool × Bool -> Real)
    (leftMarginal rightMarginal : Real)
    (model :
      IsIndependentEventCoupling mass leftMarginal rightMarginal) :
    jointEventMass mass = leftMarginal * rightMarginal := by
  have left_off_diagonal :
      mass (true, false) =
        leftMarginal - mass (true, true) := by
    linarith [model.1.leftMarginalEq]
  have right_off_diagonal :
      mass (false, true) =
        rightMarginal - mass (true, true) := by
    linarith [model.1.rightMarginalEq]
  have neither_event :
      mass (false, false) =
        1 - leftMarginal - rightMarginal + mass (true, true) := by
    linarith [
      model.1.total,
      model.1.leftMarginalEq,
      model.1.rightMarginalEq
    ]
  have determinant := model.2
  rw [
    neither_event,
    left_off_diagonal,
    right_off_diagonal
  ] at determinant
  dsimp [jointEventMass]
  nlinarith

/-- For probability-valued marginals, the product coupling is a normalized
nonnegative independent event coupling. -/
theorem eventCoupling_isIndependent
    (leftMarginal rightMarginal : Real)
    (left_nonnegative : 0 <= leftMarginal)
    (left_at_most_one : leftMarginal <= 1)
    (right_nonnegative : 0 <= rightMarginal)
    (right_at_most_one : rightMarginal <= 1) :
    IsIndependentEventCoupling
      (eventCoupling
        leftMarginal rightMarginal
        (leftMarginal * rightMarginal))
      leftMarginal rightMarginal := by
  have product_nonnegative :
      0 <= leftMarginal * rightMarginal :=
    mul_nonneg left_nonnegative right_nonnegative
  have complement_product_nonnegative :
      0 <= (1 - leftMarginal) * (1 - rightMarginal) :=
    mul_nonneg
      (sub_nonneg.mpr left_at_most_one)
      (sub_nonneg.mpr right_at_most_one)
  have frechet_lower :
      leftMarginal + rightMarginal - 1 <=
        leftMarginal * rightMarginal := by
    nlinarith
  have lower :
      max 0 (leftMarginal + rightMarginal - 1) <=
        leftMarginal * rightMarginal := by
    rw [max_le_iff]
    exact ⟨product_nonnegative, frechet_lower⟩
  have left_product_upper :
      leftMarginal * rightMarginal <= leftMarginal := by
    have h : 0 <= leftMarginal * (1 - rightMarginal) :=
      mul_nonneg left_nonnegative (sub_nonneg.mpr right_at_most_one)
    nlinarith
  have right_product_upper :
      leftMarginal * rightMarginal <= rightMarginal := by
    have h : 0 <= (1 - leftMarginal) * rightMarginal :=
      mul_nonneg (sub_nonneg.mpr left_at_most_one) right_nonnegative
    nlinarith
  have upper :
      leftMarginal * rightMarginal <=
        min leftMarginal rightMarginal := by
    rw [le_min_iff]
    exact ⟨left_product_upper, right_product_upper⟩
  constructor
  · exact eventCoupling_isEventCoupling
      leftMarginal rightMarginal
      (leftMarginal * rightMarginal) lower upper
  · simp [IndependentDeterminant, eventCoupling]
    ring

/-- Under the polynomial independence restriction, the identified range of the
joint event query is the sharp singleton containing the product of marginals. -/
theorem independent_joint_event_sharp_singleton_iff
    (leftMarginal rightMarginal target : Real)
    (left_nonnegative : 0 <= leftMarginal)
    (left_at_most_one : leftMarginal <= 1)
    (right_nonnegative : 0 <= rightMarginal)
    (right_at_most_one : rightMarginal <= 1) :
    target = leftMarginal * rightMarginal <->
      exists mass : Bool × Bool -> Real,
        IsIndependentEventCoupling
            mass leftMarginal rightMarginal /\
          jointEventMass mass = target := by
  constructor
  · intro target_eq
    refine
      ⟨eventCoupling
          leftMarginal rightMarginal
          (leftMarginal * rightMarginal),
        eventCoupling_isIndependent
          leftMarginal rightMarginal
          left_nonnegative left_at_most_one
          right_nonnegative right_at_most_one, ?_⟩
    simp [jointEventMass, eventCoupling, target_eq]
  · rintro ⟨mass, model, query_eq⟩
    calc
      target = jointEventMass mass := query_eq.symm
      _ = leftMarginal * rightMarginal :=
        independent_joint_event_eq_product
          mass leftMarginal rightMarginal model

/-- Pointwise midpoint of two four-cell laws. -/
def midpointMass
    (left right : Bool × Bool -> Real) :
    Bool × Bool -> Real :=
  fun pair => (left pair + right pair) / 2

/-- The global family of independent Boolean couplings is not convex. Two
normalized independent endpoint laws have a normalized midpoint whose
polynomial determinant is nonzero. -/
theorem independent_event_couplings_not_closed_under_midpoint :
    IsIndependentEventCoupling (eventCoupling 0 0 0) 0 0 /\
      IsIndependentEventCoupling (eventCoupling 1 1 1) 1 1 /\
      IsEventCoupling
        (midpointMass
          (eventCoupling 0 0 0)
          (eventCoupling 1 1 1))
        (1 / 2 : Real) (1 / 2 : Real) /\
      ¬IndependentDeterminant
        (midpointMass
          (eventCoupling 0 0 0)
          (eventCoupling 1 1 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact eventCoupling_isIndependent 0 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact eventCoupling_isIndependent 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · refine
      { nonnegative := ?_
        total := ?_
        leftMarginalEq := ?_
        rightMarginalEq := ?_ }
    · intro pair
      rcases pair with ⟨left, right⟩
      cases left <;> cases right <;>
        norm_num [midpointMass, eventCoupling]
    · norm_num [midpointMass, eventCoupling]
    · norm_num [midpointMass, eventCoupling]
    · norm_num [midpointMass, eventCoupling]
  · norm_num [IndependentDeterminant, midpointMass, eventCoupling]

#print axioms independent_joint_event_eq_product
#print axioms independent_joint_event_sharp_singleton_iff
#print axioms independent_event_couplings_not_closed_under_midpoint

end D5.S3.ConceptDynamics.Causal.CrossWorldIndependenceSharpBounds

/- GID: D5/S0/Certificates/LinearObjectiveDual
   generality: G
   mirror-B: D5/B/S0/Certificates/LinearObjectiveDual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact rational row multipliers certify finite linear objective bounds and endpoint optimality. -/

import D5.S0.Certificates.RationalFarkas

/- Library-search audit trail (2026-09-03):
   * `RationalFarkas` certifies infeasibility of `A x <= b` by exact rational
     row multipliers, but it does not expose weak-duality certificates for a
     nonzero linear objective.
   * Repository searches found no reusable upper-bound or lower-bound
     certificate carrying both a row representation of the objective and a
     weighted right-hand-side bound.
   * This module keeps all arithmetic rational. An external LP solver may
     propose weights and primal points, while Lean replays feasibility,
     weak duality, and endpoint attainment exactly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.LinearObjectiveDual

open scoped BigOperators
open D5.S0.Certificates.RationalFarkas

/-- Evaluation of a finite rational linear objective. -/
def linearObjective
    {Variable : Type*} [Fintype Variable]
    (coefficient point : Variable -> ℚ) : ℚ :=
  ∑ variable, coefficient variable * point variable

/-- A dual certificate for the universal upper bound `c x <= upper` over
`A x <= b`. The nonnegative row combination represents the objective and its
weighted right-hand side is at most the claimed bound. -/
structure UpperBoundCertificate
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ)
    (b : Constraint -> ℚ)
    (coefficient : Variable -> ℚ)
    (upper : ℚ) where
  weight : Constraint -> ℚ
  nonnegative : forall constraint, 0 <= weight constraint
  representsObjective : forall variable,
    (∑ constraint, weight constraint * A constraint variable) =
      coefficient variable
  weightedRhs :
    (∑ constraint, weight constraint * b constraint) <= upper

/-- A dual certificate for the universal lower bound `lower <= c x`. It
represents the negated objective by a nonnegative row combination. -/
structure LowerBoundCertificate
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ)
    (b : Constraint -> ℚ)
    (coefficient : Variable -> ℚ)
    (lower : ℚ) where
  weight : Constraint -> ℚ
  nonnegative : forall constraint, 0 <= weight constraint
  representsNegativeObjective : forall variable,
    (∑ constraint, weight constraint * A constraint variable) =
      -coefficient variable
  weightedRhs :
    (∑ constraint, weight constraint * b constraint) <= -lower

/-- An exact rational primal point attaining a nominated objective value. -/
structure PrimalWitness
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ)
    (b : Constraint -> ℚ)
    (coefficient : Variable -> ℚ)
    (value : ℚ) where
  point : Variable -> ℚ
  feasible : LinearFeasible A b point
  objectiveEq : linearObjective coefficient point = value

/-- Exactness of a lower endpoint means universal validity plus an attaining
primal point. -/
def IsExactLowerBound
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ)
    (b : Constraint -> ℚ)
    (coefficient : Variable -> ℚ)
    (lower : ℚ) : Prop :=
  (forall point,
      LinearFeasible A b point ->
        lower <= linearObjective coefficient point) /\
    exists point,
      LinearFeasible A b point /\
        linearObjective coefficient point = lower

/-- Exactness of an upper endpoint means universal validity plus an attaining
primal point. -/
def IsExactUpperBound
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ)
    (b : Constraint -> ℚ)
    (coefficient : Variable -> ℚ)
    (upper : ℚ) : Prop :=
  (forall point,
      LinearFeasible A b point ->
        linearObjective coefficient point <= upper) /\
    exists point,
      LinearFeasible A b point /\
        linearObjective coefficient point = upper

/-- Nonnegative row multipliers preserve every feasible inequality after
finite weighted summation. -/
theorem weighted_constraint_bound
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ)
    (b : Constraint -> ℚ)
    (weight : Constraint -> ℚ)
    (weight_nonnegative : forall constraint, 0 <= weight constraint)
    (point : Variable -> ℚ)
    (feasible : LinearFeasible A b point) :
    (∑ constraint,
        weight constraint *
          (∑ variable, A constraint variable * point variable)) <=
      ∑ constraint, weight constraint * b constraint := by
  have weighted (constraint : Constraint) :
      weight constraint *
          (∑ variable, A constraint variable * point variable) <=
        weight constraint * b constraint :=
    mul_le_mul_of_nonneg_left
      (feasible constraint) (weight_nonnegative constraint)
  exact Finset.sum_le_sum fun constraint _ => weighted constraint

/-- If the weighted rows represent an objective, their weighted left side is
exactly that objective at every primal point. -/
theorem weighted_constraint_sum_eq_objective
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ)
    (coefficient : Variable -> ℚ)
    (weight : Constraint -> ℚ)
    (represents : forall variable,
      (∑ constraint, weight constraint * A constraint variable) =
        coefficient variable)
    (point : Variable -> ℚ) :
    (∑ constraint,
        weight constraint *
          (∑ variable, A constraint variable * point variable)) =
      linearObjective coefficient point := by
  calc
    (∑ constraint,
        weight constraint *
          (∑ variable, A constraint variable * point variable)) =
        ∑ constraint, ∑ variable,
          weight constraint *
            (A constraint variable * point variable) := by
      apply Finset.sum_congr rfl
      intro constraint _
      rw [Finset.mul_sum]
    _ = ∑ variable, ∑ constraint,
          weight constraint *
            (A constraint variable * point variable) := by
      rw [Finset.sum_comm]
    _ = ∑ variable,
          (∑ constraint,
            weight constraint * A constraint variable) *
              point variable := by
      apply Finset.sum_congr rfl
      intro variable _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro constraint _
      ring
    _ = ∑ variable, coefficient variable * point variable := by
      apply Finset.sum_congr rfl
      intro variable _
      rw [represents variable]
    _ = linearObjective coefficient point := rfl

/-- Negating every objective coefficient negates its finite evaluation. -/
theorem linearObjective_neg
    {Variable : Type*} [Fintype Variable]
    (coefficient point : Variable -> ℚ) :
    linearObjective (fun variable => -coefficient variable) point =
      -linearObjective coefficient point := by
  simp [linearObjective]

/-- Exact rational upper dual certificates prove universal objective bounds. -/
theorem upper_bound_of_certificate
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ)
    (b : Constraint -> ℚ)
    (coefficient : Variable -> ℚ)
    (upper : ℚ)
    (certificate : UpperBoundCertificate A b coefficient upper)
    (point : Variable -> ℚ)
    (feasible : LinearFeasible A b point) :
    linearObjective coefficient point <= upper := by
  have summed :=
    weighted_constraint_bound
      A b certificate.weight certificate.nonnegative point feasible
  have represented :=
    weighted_constraint_sum_eq_objective
      A coefficient certificate.weight
      certificate.representsObjective point
  rw [represented] at summed
  exact summed.trans certificate.weightedRhs

/-- Exact rational lower dual certificates prove universal objective bounds. -/
theorem lower_bound_of_certificate
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ)
    (b : Constraint -> ℚ)
    (coefficient : Variable -> ℚ)
    (lower : ℚ)
    (certificate : LowerBoundCertificate A b coefficient lower)
    (point : Variable -> ℚ)
    (feasible : LinearFeasible A b point) :
    lower <= linearObjective coefficient point := by
  have summed :=
    weighted_constraint_bound
      A b certificate.weight certificate.nonnegative point feasible
  have represented :=
    weighted_constraint_sum_eq_objective
      A (fun variable => -coefficient variable)
      certificate.weight certificate.representsNegativeObjective point
  rw [represented, linearObjective_neg] at summed
  have negated :
      -linearObjective coefficient point <= -lower :=
    summed.trans certificate.weightedRhs
  linarith

/-- A valid lower dual certificate and a matching primal witness certify the
exact lower endpoint. -/
theorem exact_lower_bound_of_certificate_and_witness
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ)
    (b : Constraint -> ℚ)
    (coefficient : Variable -> ℚ)
    (lower : ℚ)
    (certificate : LowerBoundCertificate A b coefficient lower)
    (witness : PrimalWitness A b coefficient lower) :
    IsExactLowerBound A b coefficient lower := by
  constructor
  · intro point feasible
    exact lower_bound_of_certificate
      A b coefficient lower certificate point feasible
  · exact ⟨witness.point, witness.feasible, witness.objectiveEq⟩

/-- A valid upper dual certificate and a matching primal witness certify the
exact upper endpoint. -/
theorem exact_upper_bound_of_certificate_and_witness
    {Constraint Variable : Type*}
    [Fintype Constraint] [Fintype Variable]
    (A : Constraint -> Variable -> ℚ)
    (b : Constraint -> ℚ)
    (coefficient : Variable -> ℚ)
    (upper : ℚ)
    (certificate : UpperBoundCertificate A b coefficient upper)
    (witness : PrimalWitness A b coefficient upper) :
    IsExactUpperBound A b coefficient upper := by
  constructor
  · intro point feasible
    exact upper_bound_of_certificate
      A b coefficient upper certificate point feasible
  · exact ⟨witness.point, witness.feasible, witness.objectiveEq⟩

#print axioms upper_bound_of_certificate
#print axioms lower_bound_of_certificate
#print axioms exact_lower_bound_of_certificate_and_witness
#print axioms exact_upper_bound_of_certificate_and_witness

end D5.S0.Certificates.LinearObjectiveDual

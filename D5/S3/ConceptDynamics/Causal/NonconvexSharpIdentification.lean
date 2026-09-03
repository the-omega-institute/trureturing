/- GID: D5/S3/ConceptDynamics/Causal/NonconvexSharpIdentification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/NonconvexSharpIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonconvex identified sets require direct range witnesses beyond endpoint attainment. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-09-03):
   * `ConvexSharpIdentification` proves that convex feasibility and an affine
     query fill the interval between two attaining endpoint models.
   * Repository searches found no weaker identification core for nonlinear or
     semialgebraic feasible sets, and no formal counterexample showing why the
     convex interpolation hypothesis cannot simply be dropped.
   * Cross-world factorization assumptions produce polynomial equalities whose
     feasible sets need not be convex. This module therefore separates endpoint
     exactness, outer-relaxation validity, and full range sharpness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.NonconvexSharpIdentification

/-- A scalar partial-identification problem with no convexity assumption. -/
structure IdentificationProblem (Model : Type) where
  feasible : Model -> Prop
  query : Model -> Real

/-- Every feasible model lies above a valid lower bound. -/
def IsValidLowerBound {Model : Type}
    (problem : IdentificationProblem Model)
    (lower : Real) : Prop :=
  forall model, problem.feasible model -> lower <= problem.query model

/-- Every feasible model lies below a valid upper bound. -/
def IsValidUpperBound {Model : Type}
    (problem : IdentificationProblem Model)
    (upper : Real) : Prop :=
  forall model, problem.feasible model -> problem.query model <= upper

/-- A lower endpoint is exact when it is universally valid and attained. -/
def IsExactLowerEndpoint {Model : Type}
    (problem : IdentificationProblem Model)
    (lower : Real) : Prop :=
  IsValidLowerBound problem lower /\
    exists model,
      problem.feasible model /\ problem.query model = lower

/-- An upper endpoint is exact when it is universally valid and attained. -/
def IsExactUpperEndpoint {Model : Type}
    (problem : IdentificationProblem Model)
    (upper : Real) : Prop :=
  IsValidUpperBound problem upper /\
    exists model,
      problem.feasible model /\ problem.query model = upper

/-- The complete identified range is sharp when its predicate agrees exactly
with the values achieved by feasible models. This allows disconnected ranges. -/
def IsSharpRange {Model : Type}
    (problem : IdentificationProblem Model)
    (range : Real -> Prop) : Prop :=
  forall target,
    range target <->
      exists model,
        problem.feasible model /\ problem.query model = target

/-- A closed interval is sharp when every and only feasible query values lie in
that interval. No convexity is built into this definition. -/
def IsSharpInterval {Model : Type}
    (problem : IdentificationProblem Model)
    (lower upper : Real) : Prop :=
  IsSharpRange problem (fun target => lower <= target /\ target <= upper)

/-- A universal lower certificate and one attaining model prove an exact lower
endpoint without any convexity assumption. -/
theorem exact_lower_endpoint_of_valid_bound_and_witness
    {Model : Type}
    (problem : IdentificationProblem Model)
    (lower : Real)
    (valid : IsValidLowerBound problem lower)
    (witness : Model)
    (witness_feasible : problem.feasible witness)
    (witness_value : problem.query witness = lower) :
    IsExactLowerEndpoint problem lower := by
  exact ⟨valid, ⟨witness, witness_feasible, witness_value⟩⟩

/-- The analogous endpoint theorem for an upper bound. -/
theorem exact_upper_endpoint_of_valid_bound_and_witness
    {Model : Type}
    (problem : IdentificationProblem Model)
    (upper : Real)
    (valid : IsValidUpperBound problem upper)
    (witness : Model)
    (witness_feasible : problem.feasible witness)
    (witness_value : problem.query witness = upper) :
    IsExactUpperEndpoint problem upper := by
  exact ⟨valid, ⟨witness, witness_feasible, witness_value⟩⟩

/-- A lower bound proved on an outer relaxation remains valid on every inner
feasible family. -/
theorem valid_lower_bound_of_outer_relaxation
    {Model : Type}
    (inner outer : IdentificationProblem Model)
    (same_query : forall model, inner.query model = outer.query model)
    (contained : forall model, inner.feasible model -> outer.feasible model)
    (lower : Real)
    (outer_valid : IsValidLowerBound outer lower) :
    IsValidLowerBound inner lower := by
  intro model feasible
  rw [same_query model]
  exact outer_valid model (contained model feasible)

/-- An upper bound proved on an outer relaxation remains valid on every inner
feasible family. -/
theorem valid_upper_bound_of_outer_relaxation
    {Model : Type}
    (inner outer : IdentificationProblem Model)
    (same_query : forall model, inner.query model = outer.query model)
    (contained : forall model, inner.feasible model -> outer.feasible model)
    (upper : Real)
    (outer_valid : IsValidUpperBound outer upper) :
    IsValidUpperBound inner upper := by
  intro model feasible
  rw [same_query model]
  exact outer_valid model (contained model feasible)

/-- If an inner nonlinear model attains a lower value, every valid lower bound
of an outer relaxation must lie below it. -/
theorem outer_lower_bound_below_inner_witness
    {Model : Type}
    (inner outer : IdentificationProblem Model)
    (same_query : forall model, inner.query model = outer.query model)
    (contained : forall model, inner.feasible model -> outer.feasible model)
    (outerLower innerValue : Real)
    (outer_valid : IsValidLowerBound outer outerLower)
    (innerWitness : Model)
    (inner_feasible : inner.feasible innerWitness)
    (inner_value : inner.query innerWitness = innerValue) :
    outerLower <= innerValue := by
  have h := outer_valid innerWitness (contained innerWitness inner_feasible)
  rw [← same_query innerWitness] at h
  simpa [inner_value] using h

/-- If an inner nonlinear model attains an upper value, every valid upper bound
of an outer relaxation must lie above it. -/
theorem inner_witness_below_outer_upper_bound
    {Model : Type}
    (inner outer : IdentificationProblem Model)
    (same_query : forall model, inner.query model = outer.query model)
    (contained : forall model, inner.feasible model -> outer.feasible model)
    (outerUpper innerValue : Real)
    (outer_valid : IsValidUpperBound outer outerUpper)
    (innerWitness : Model)
    (inner_feasible : inner.feasible innerWitness)
    (inner_value : inner.query innerWitness = innerValue) :
    innerValue <= outerUpper := by
  have h := outer_valid innerWitness (contained innerWitness inner_feasible)
  rw [← same_query innerWitness] at h
  simpa [inner_value] using h

/-- A two-point feasible family is the minimal disconnected identified set. -/
def twoPointProblem : IdentificationProblem Real where
  feasible value := value = 0 \/ value = 2
  query value := value

/-- Both endpoints of the two-point problem are exact. -/
theorem twoPointProblem_exact_endpoints :
    IsExactLowerEndpoint twoPointProblem 0 /\
      IsExactUpperEndpoint twoPointProblem 2 := by
  constructor
  · constructor
    · intro value feasible
      rcases feasible with rfl | rfl <;> norm_num
    · exact ⟨0, Or.inl rfl, rfl⟩
  · constructor
    · intro value feasible
      rcases feasible with rfl | rfl <;> norm_num
    · exact ⟨2, Or.inr rfl, rfl⟩

/-- Exact attainment of both endpoints does not imply that the intervening
interval is sharp. The target one lies between zero and two but is unattained. -/
theorem endpoint_attainment_without_convexity_does_not_fill_interval :
    ¬IsSharpInterval twoPointProblem 0 2 := by
  intro sharp
  have realized := (sharp 1).mp ⟨by norm_num, by norm_num⟩
  rcases realized with ⟨value, feasible, query_eq⟩
  rcases feasible with value_zero | value_two
  · rw [value_zero] at query_eq
    norm_num at query_eq
  · rw [value_two] at query_eq
    norm_num at query_eq

#print axioms exact_lower_endpoint_of_valid_bound_and_witness
#print axioms valid_lower_bound_of_outer_relaxation
#print axioms endpoint_attainment_without_convexity_does_not_fill_interval

end D5.S3.ConceptDynamics.Causal.NonconvexSharpIdentification

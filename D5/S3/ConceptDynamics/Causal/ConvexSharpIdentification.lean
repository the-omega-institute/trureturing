/- GID: D5/S3/ConceptDynamics/Causal/ConvexSharpIdentification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/ConvexSharpIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Convex feasible models and affine queries turn attained endpoint bounds into a sharp interval. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Library-search audit trail (2026-09-03):
   * The causal lane contains concrete Boolean and finite coupling sharp bounds.
   * Repository search found no generic theorem separating valid bounds, endpoint
     attainment, convex feasibility, affine queries, and interval sharpness.
   * This module is deliberately causal-agnostic. It supplies the logical theorem
     that finite causal LP instances can invoke after proving their compiler sound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.ConvexSharpIdentification

/-- A scalar partial-identification problem equipped with an abstract convex
blend operation and an affine scalar query. -/
structure ConvexIdentificationProblem (Model : Type) where
  feasible : Model -> Prop
  query : Model -> Real
  blend : Real -> Model -> Model -> Model
  feasible_blend :
    forall (t : Real) (left right : Model),
      0 <= t -> t <= 1 ->
      feasible left -> feasible right ->
      feasible (blend t left right)
  query_blend :
    forall (t : Real) (left right : Model),
      query (blend t left right) =
        (1 - t) * query left + t * query right

/-- A lower endpoint is valid when every admissible model lies above it. -/
def IsValidLowerBound {Model : Type}
    (problem : ConvexIdentificationProblem Model)
    (lower : Real) : Prop :=
  forall model, problem.feasible model -> lower <= problem.query model

/-- An upper endpoint is valid when every admissible model lies below it. -/
def IsValidUpperBound {Model : Type}
    (problem : ConvexIdentificationProblem Model)
    (upper : Real) : Prop :=
  forall model, problem.feasible model -> problem.query model <= upper

/-- A scalar interval is sharp when its targets are exactly the query values of
admissible models. -/
def IsSharpInterval {Model : Type}
    (problem : ConvexIdentificationProblem Model)
    (lower upper : Real) : Prop :=
  forall target,
    (lower <= target /\ target <= upper) <->
      exists model,
        problem.feasible model /\ problem.query model = target

/-- A universal valid bound plus an attaining primal witness makes the lower
endpoint exact. This theorem isolates the logical role of primal attainment
from whatever mechanism produced the universal certificate. -/
theorem exact_lower_endpoint_of_valid_bound_and_witness
    {Model : Type}
    (problem : ConvexIdentificationProblem Model)
    (lower : Real)
    (valid : IsValidLowerBound problem lower)
    (witness : Model)
    (witness_feasible : problem.feasible witness)
    (witness_value : problem.query witness = lower) :
    IsValidLowerBound problem lower /\
      exists model,
        problem.feasible model /\ problem.query model = lower := by
  exact ⟨valid, ⟨witness, witness_feasible, witness_value⟩⟩

/-- The analogous primal-certificate statement for an upper endpoint. -/
theorem exact_upper_endpoint_of_valid_bound_and_witness
    {Model : Type}
    (problem : ConvexIdentificationProblem Model)
    (upper : Real)
    (valid : IsValidUpperBound problem upper)
    (witness : Model)
    (witness_feasible : problem.feasible witness)
    (witness_value : problem.query witness = upper) :
    IsValidUpperBound problem upper /\
      exists model,
        problem.feasible model /\ problem.query model = upper := by
  exact ⟨valid, ⟨witness, witness_feasible, witness_value⟩⟩

/-- Convexity and affinity upgrade two attained valid endpoints to a complete
sharp identified interval. Interior targets are realized by mixing the two
endpoint models. -/
theorem sharp_interval_of_valid_bounds_and_endpoint_witnesses
    {Model : Type}
    (problem : ConvexIdentificationProblem Model)
    (lower upper : Real)
    (valid_lower : IsValidLowerBound problem lower)
    (valid_upper : IsValidUpperBound problem upper)
    (lowerModel upperModel : Model)
    (lower_feasible : problem.feasible lowerModel)
    (upper_feasible : problem.feasible upperModel)
    (lower_value : problem.query lowerModel = lower)
    (upper_value : problem.query upperModel = upper) :
    IsSharpInterval problem lower upper := by
  have lower_le_upper : lower <= upper := by
    have h := valid_upper lowerModel lower_feasible
    simpa [lower_value] using h
  intro target
  constructor
  · intro target_bounds
    by_cases endpoints_equal : lower = upper
    · have target_eq : target = lower := by
        linarith [target_bounds.1, target_bounds.2]
      exact
        ⟨lowerModel, lower_feasible,
          by simpa [target_eq] using lower_value⟩
    · have endpoints_lt : lower < upper :=
        lt_of_le_of_ne lower_le_upper endpoints_equal
      let t : Real := (target - lower) / (upper - lower)
      have denominator_positive : 0 < upper - lower := sub_pos.mpr endpoints_lt
      have t_nonnegative : 0 <= t := by
        dsimp [t]
        exact div_nonneg (sub_nonneg.mpr target_bounds.1)
          (le_of_lt denominator_positive)
      have numerator_le_denominator :
          target - lower <= upper - lower := by
        linarith [target_bounds.2]
      have t_le_one : t <= 1 := by
        dsimp [t]
        exact (div_le_one denominator_positive).2 numerator_le_denominator
      refine
        ⟨problem.blend t lowerModel upperModel,
          problem.feasible_blend t lowerModel upperModel
            t_nonnegative t_le_one lower_feasible upper_feasible, ?_⟩
      rw [problem.query_blend, lower_value, upper_value]
      dsimp [t]
      have denominator_ne : upper - lower != 0 := ne_of_gt denominator_positive
      field_simp [denominator_ne]
      ring
  · rintro ⟨model, feasible, query_eq⟩
    constructor
    · have h := valid_lower model feasible
      simpa [query_eq] using h
    · have h := valid_upper model feasible
      simpa [query_eq] using h

/-- A valid lower bound survives restriction to a stronger feasible family. -/
theorem valid_lower_bound_of_feasible_refinement
    {Model : Type}
    (weaker stronger : ConvexIdentificationProblem Model)
    (same_query : forall model, stronger.query model = weaker.query model)
    (refines : forall model, stronger.feasible model -> weaker.feasible model)
    (lower : Real)
    (valid : IsValidLowerBound weaker lower) :
    IsValidLowerBound stronger lower := by
  intro model feasible
  rw [same_query model]
  exact valid model (refines model feasible)

/-- A valid upper bound likewise survives feasible-set restriction. -/
theorem valid_upper_bound_of_feasible_refinement
    {Model : Type}
    (weaker stronger : ConvexIdentificationProblem Model)
    (same_query : forall model, stronger.query model = weaker.query model)
    (refines : forall model, stronger.feasible model -> weaker.feasible model)
    (upper : Real)
    (valid : IsValidUpperBound weaker upper) :
    IsValidUpperBound stronger upper := by
  intro model feasible
  rw [same_query model]
  exact valid model (refines model feasible)

/-- Exact endpoint witnesses make the information-order statement quantitative:
stronger assumptions can only raise the exact lower endpoint. -/
theorem exact_lower_endpoint_monotone_under_refinement
    {Model : Type}
    (weaker stronger : ConvexIdentificationProblem Model)
    (same_query : forall model, stronger.query model = weaker.query model)
    (refines : forall model, stronger.feasible model -> weaker.feasible model)
    (weakerLower strongerLower : Real)
    (weaker_valid : IsValidLowerBound weaker weakerLower)
    (strongerWitness : Model)
    (stronger_feasible : stronger.feasible strongerWitness)
    (stronger_value : stronger.query strongerWitness = strongerLower) :
    weakerLower <= strongerLower := by
  have h := weaker_valid strongerWitness (refines strongerWitness stronger_feasible)
  rw [← same_query strongerWitness] at h
  simpa [stronger_value] using h

/-- Stronger assumptions can only lower the exact upper endpoint. -/
theorem exact_upper_endpoint_monotone_under_refinement
    {Model : Type}
    (weaker stronger : ConvexIdentificationProblem Model)
    (same_query : forall model, stronger.query model = weaker.query model)
    (refines : forall model, stronger.feasible model -> weaker.feasible model)
    (weakerUpper strongerUpper : Real)
    (weaker_valid : IsValidUpperBound weaker weakerUpper)
    (strongerWitness : Model)
    (stronger_feasible : stronger.feasible strongerWitness)
    (stronger_value : stronger.query strongerWitness = strongerUpper) :
    strongerUpper <= weakerUpper := by
  have h := weaker_valid strongerWitness (refines strongerWitness stronger_feasible)
  rw [← same_query strongerWitness] at h
  simpa [stronger_value] using h

#print axioms sharp_interval_of_valid_bounds_and_endpoint_witnesses
#print axioms exact_lower_endpoint_monotone_under_refinement
#print axioms exact_upper_endpoint_monotone_under_refinement

end D5.S3.ConceptDynamics.Causal.ConvexSharpIdentification

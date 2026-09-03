/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/CovariateSharpAggregation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/CovariateSharpAggregation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Independently combinable covariate-stratum sharp intervals aggregate to an exact weighted sharp interval. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Nlinarith

/- Library-search audit trail (2026-09-03):
   * `ConvexSharpIdentification` proves interval filling for one convex model
     family, but it does not package independently combinable covariate strata.
   * Repository searches for weighted sharp intervals, covariate aggregation,
     and stratum-specific identification returned no reusable truth source.
   * The theorem below keeps the essential causal assumption explicit:
     stratum-level attainable values may be selected jointly. Shared parameters
     or cross-stratum restrictions require a different feasible family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.CovariateSharpAggregation

open scoped BigOperators

/-- Weighted aggregation of scalar stratum values. Probability weights are the
causal application, while the theorem only requires nonnegative weights. -/
def weightedValue
    {Covariate : Type*} [Fintype Covariate]
    (weight value : Covariate -> Real) : Real :=
  ∑ covariate, weight covariate * value covariate

/-- A family of exact stratum-level identified intervals. `attainable c q`
means that some admissible model in stratum `c` realizes query value `q`. -/
structure StratifiedSharpFamily
    (Covariate : Type*) [Fintype Covariate] where
  attainable : Covariate -> Real -> Prop
  lower : Covariate -> Real
  upper : Covariate -> Real
  lower_le_upper : forall covariate, lower covariate <= upper covariate
  sharp : forall covariate target,
    (lower covariate <= target /\ target <= upper covariate) <->
      attainable covariate target

/-- Global attainability under independent stratum combination. A witness
chooses one attainable query value in every stratum and then aggregates it. -/
def GloballyAttainable
    {Covariate : Type*} [Fintype Covariate]
    (family : StratifiedSharpFamily Covariate)
    (weight : Covariate -> Real)
    (target : Real) : Prop :=
  exists value : Covariate -> Real,
    (forall covariate, family.attainable covariate (value covariate)) /\
      weightedValue weight value = target

/-- Nonnegative weights preserve pointwise order under finite aggregation. -/
theorem weightedValue_mono
    {Covariate : Type*} [Fintype Covariate]
    (weight left right : Covariate -> Real)
    (weight_nonnegative : forall covariate, 0 <= weight covariate)
    (pointwise : forall covariate, left covariate <= right covariate) :
    weightedValue weight left <= weightedValue weight right := by
  unfold weightedValue
  exact Finset.sum_le_sum fun covariate _ =>
    mul_le_mul_of_nonneg_left
      (pointwise covariate) (weight_nonnegative covariate)

/-- Weighted aggregation is affine under a common interpolation parameter. -/
theorem weightedValue_blend
    {Covariate : Type*} [Fintype Covariate]
    (weight left right : Covariate -> Real)
    (t : Real) :
    weightedValue weight
        (fun covariate =>
          (1 - t) * left covariate + t * right covariate) =
      (1 - t) * weightedValue weight left +
        t * weightedValue weight right := by
  unfold weightedValue
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro covariate _
  ring

/-- If every stratum interval is sharp and stratum witnesses can be selected
jointly, then the weighted covariate-adjusted query has the exact interval
whose endpoints are the weighted stratum endpoints. A common interpolation
parameter realizes every interior global target. -/
theorem covariate_weighted_sharp_iff
    {Covariate : Type*} [Fintype Covariate]
    (family : StratifiedSharpFamily Covariate)
    (weight : Covariate -> Real)
    (weight_nonnegative : forall covariate, 0 <= weight covariate)
    (target : Real) :
    (weightedValue weight family.lower <= target /\
        target <= weightedValue weight family.upper) <->
      GloballyAttainable family weight target := by
  have endpoint_order :
      weightedValue weight family.lower <=
        weightedValue weight family.upper :=
    weightedValue_mono weight family.lower family.upper
      weight_nonnegative family.lower_le_upper
  constructor
  · intro target_bounds
    by_cases endpoints_equal :
        weightedValue weight family.lower =
          weightedValue weight family.upper
    · have target_eq :
          target = weightedValue weight family.lower := by
        linarith [target_bounds.1, target_bounds.2]
      refine ⟨family.lower, ?_, target_eq.symm⟩
      intro covariate
      exact (family.sharp covariate (family.lower covariate)).mp
        ⟨le_rfl, family.lower_le_upper covariate⟩
    · have endpoints_lt :
          weightedValue weight family.lower <
            weightedValue weight family.upper :=
        lt_of_le_of_ne endpoint_order endpoints_equal
      let t : Real :=
        (target - weightedValue weight family.lower) /
          (weightedValue weight family.upper -
            weightedValue weight family.lower)
      have denominator_positive :
          0 < weightedValue weight family.upper -
            weightedValue weight family.lower :=
        sub_pos.mpr endpoints_lt
      have denominator_ne :
          weightedValue weight family.upper -
              weightedValue weight family.lower != 0 :=
        ne_of_gt denominator_positive
      have t_nonnegative : 0 <= t := by
        dsimp [t]
        exact div_nonneg
          (sub_nonneg.mpr target_bounds.1)
          (le_of_lt denominator_positive)
      have numerator_le_denominator :
          target - weightedValue weight family.lower <=
            weightedValue weight family.upper -
              weightedValue weight family.lower := by
        linarith [target_bounds.2]
      have t_le_one : t <= 1 := by
        dsimp [t]
        exact (div_le_one denominator_positive).2
          numerator_le_denominator
      let value : Covariate -> Real := fun covariate =>
        (1 - t) * family.lower covariate +
          t * family.upper covariate
      refine ⟨value, ?_, ?_⟩
      · intro covariate
        apply (family.sharp covariate (value covariate)).mp
        have stratum_order := family.lower_le_upper covariate
        have lower_gap_nonnegative :
            0 <= t *
              (family.upper covariate - family.lower covariate) :=
          mul_nonneg t_nonnegative (sub_nonneg.mpr stratum_order)
        have upper_gap_nonnegative :
            0 <= (1 - t) *
              (family.upper covariate - family.lower covariate) :=
          mul_nonneg (sub_nonneg.mpr t_le_one)
            (sub_nonneg.mpr stratum_order)
        constructor <;> dsimp [value] <;> nlinarith
      · rw [weightedValue_blend]
        have t_relation :
            t *
                (weightedValue weight family.upper -
                  weightedValue weight family.lower) =
              target - weightedValue weight family.lower := by
          dsimp [t]
          field_simp [denominator_ne]
        nlinarith [t_relation]
  · rintro ⟨value, attainable, query_eq⟩
    have pointwise_bounds : forall covariate,
        family.lower covariate <= value covariate /\
          value covariate <= family.upper covariate := by
      intro covariate
      exact (family.sharp covariate (value covariate)).mpr
        (attainable covariate)
    have lower_bound :
        weightedValue weight family.lower <=
          weightedValue weight value :=
      weightedValue_mono weight family.lower value
        weight_nonnegative (fun covariate => (pointwise_bounds covariate).1)
    have upper_bound :
        weightedValue weight value <=
          weightedValue weight family.upper :=
      weightedValue_mono weight value family.upper
        weight_nonnegative (fun covariate => (pointwise_bounds covariate).2)
    rw [query_eq] at lower_bound upper_bound
    exact ⟨lower_bound, upper_bound⟩

#print axioms covariate_weighted_sharp_iff

end D5.S3.ConceptDynamics.Causal.PartialIdentification.CovariateSharpAggregation

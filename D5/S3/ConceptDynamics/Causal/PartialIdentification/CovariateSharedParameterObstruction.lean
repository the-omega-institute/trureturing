/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/CovariateSharedParameterObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/CovariateSharedParameterObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sharp stratum projections need not aggregate sharply when strata share an unidentified parameter. -/

import D5.S3.ConceptDynamics.Causal.PartialIdentification.CovariateSharpAggregation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/- Library-search audit trail (2026-09-03):
   * `CovariateSharpAggregation` proves exact weighted aggregation under the
     explicit premise that attainable values may be selected independently in
     every stratum.
   * Repository searches found no counterexample showing that sharp stratum
     projections alone are insufficient under a shared structural parameter.
   * The two-stratum construction below has individually sharp projections
     `[0, 1]`, while one shared parameter forces the equal-weight query to the
     singleton `{1 / 2}`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.CovariateSharedParameterObstruction

open D5.S3.ConceptDynamics.Causal.PartialIdentification.CovariateSharpAggregation

/-- Two covariate strata respond in complementary ways to one common latent
parameter. -/
def localQuery (stratum : Bool) (parameter : Real) : Real :=
  if stratum then 1 - parameter else parameter

/-- Stratum-level attainability allows the parameter to be chosen separately
for the selected stratum. -/
def LocalAttainable (stratum : Bool) (target : Real) : Prop :=
  exists parameter : Real,
    0 <= parameter /\ parameter <= 1 /\
      localQuery stratum parameter = target

/-- Each stratum separately has the exact identified interval `[0, 1]`. -/
theorem local_attainable_iff
    (stratum : Bool) (target : Real) :
    (0 <= target /\ target <= 1) <->
      LocalAttainable stratum target := by
  cases stratum with
  | false =>
      constructor
      · intro bounds
        refine ⟨target, bounds.1, bounds.2, ?_⟩
        simp [localQuery]
      · rintro ⟨parameter, parameter_nonnegative,
          parameter_le_one, query_eq⟩
        simp [localQuery] at query_eq
        constructor <;> linarith
  | true =>
      constructor
      · intro bounds
        refine ⟨1 - target, ?_, ?_, ?_⟩
        · linarith [bounds.2]
        · linarith [bounds.1]
        · simp [localQuery]
      · rintro ⟨parameter, parameter_nonnegative,
          parameter_le_one, query_eq⟩
        simp [localQuery] at query_eq
        constructor <;> linarith

/-- The two individually sharp stratum problems packaged for the independent
aggregation theorem. -/
def localSharpFamily : StratifiedSharpFamily Bool where
  attainable := LocalAttainable
  lower := fun _ => 0
  upper := fun _ => 1
  lower_le_upper := by
    intro _
    norm_num
  sharp := by
    intro stratum target
    exact local_attainable_iff stratum target

/-- Equal covariate weights. -/
def halfWeight (_ : Bool) : Real := 1 / 2

/-- Under independent stratum selection, both strata can simultaneously be
assigned query value zero. -/
theorem independently_attainable_zero :
    GloballyAttainable localSharpFamily halfWeight 0 := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro stratum
    change LocalAttainable stratum 0
    exact (local_attainable_iff stratum 0).mp (by norm_num)
  · simp [weightedValue, halfWeight]

/-- The actual equal-weight query when both strata must use one common
parameter. -/
def sharedWeightedQuery (parameter : Real) : Real :=
  (1 / 2) * localQuery false parameter +
    (1 / 2) * localQuery true parameter

/-- Any fixed point of the affine complement involution `x ↦ 1 - x` is one
half. This is pure affine algebra. It carries no statement about the Riemann
zeta function or the location of its zeros. -/
theorem complement_fixed_point_eq_half
    (value : Real)
    (fixed : value = 1 - value) :
    value = 1 / 2 := by
  linarith

/-- Equal weighting sends every complementary pair whose sum is one to one
half. -/
theorem equal_weight_complementary_pair_eq_half
    (left right : Real)
    (complementary : left + right = 1) :
    (1 / 2) * left + (1 / 2) * right = 1 / 2 := by
  linarith

/-- The two local responses form a complementary pair for every shared
parameter. -/
theorem localQuery_complementary (parameter : Real) :
    localQuery false parameter + localQuery true parameter = 1 := by
  simp [localQuery]

/-- Complementary responses cancel the shared parameter exactly. -/
theorem sharedWeightedQuery_eq_half (parameter : Real) :
    sharedWeightedQuery parameter = 1 / 2 := by
  exact equal_weight_complementary_pair_eq_half
    (localQuery false parameter) (localQuery true parameter)
    (localQuery_complementary parameter)

/-- Global attainability after imposing the cross-stratum shared-parameter
constraint. -/
def SharedParameterAttainable (target : Real) : Prop :=
  exists parameter : Real,
    0 <= parameter /\ parameter <= 1 /\
      sharedWeightedQuery parameter = target

/-- The shared-parameter identified set is the singleton `{1 / 2}`. -/
theorem shared_parameter_attainable_iff (target : Real) :
    SharedParameterAttainable target <-> target = 1 / 2 := by
  constructor
  · rintro ⟨parameter, _, _, query_eq⟩
    rw [sharedWeightedQuery_eq_half] at query_eq
    exact query_eq.symm
  · intro target_eq
    refine ⟨0, by norm_num, by norm_num, ?_⟩
    rw [sharedWeightedQuery_eq_half]
    exact target_eq.symm

/-- Sharpness of all stratum projections does not justify naive weighted
sharpness when the strata share a structural parameter. The independent
product family attains zero, while the true shared-parameter family cannot. -/
theorem shared_parameter_invalidates_naive_weighted_sharpness :
    GloballyAttainable localSharpFamily halfWeight 0 /\
      not (SharedParameterAttainable 0) := by
  constructor
  · exact independently_attainable_zero
  · rw [shared_parameter_attainable_iff]
    norm_num

#print axioms local_attainable_iff
#print axioms complement_fixed_point_eq_half
#print axioms equal_weight_complementary_pair_eq_half
#print axioms shared_parameter_attainable_iff
#print axioms shared_parameter_invalidates_naive_weighted_sharpness

end D5.S3.ConceptDynamics.Causal.PartialIdentification.CovariateSharedParameterObstruction

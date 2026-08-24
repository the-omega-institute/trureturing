/- GID: D5/S3/ConceptDynamics/ResidualCoverage/GreedyResidualAllocation
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Greedy allocation maximizes one-step gain and positive witnesses force progress. -/

import D5.S3.ConceptDynamics.ResidualCoverage.WeightedResidualCoverage

/- Library-search audit trail (2026-08-24):
   * `rg -n 'IsGreedyChoice|CostEffectiveChoice|greedy_one_step_optimal|
     greedy_positive_progress' D5 --glob '*.lean'` found no repository result.
   * Pinned Mathlib searches for `single_le_sum`, `sum_pos_iff`,
     `Nat.mul_le_mul_right`, and `Nat.le_of_mul_le_mul_right` found generic
     arithmetic helpers, but no theorem about this weighted coverage carrier.
   * The uniform-cost equivalence below assumes `0 < c`. Without it, `c = 0`
     makes every cost comparison true and therefore does not imply greediness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ResidualCoverage.GreedyResidualAllocation

open D5.S3.ConceptDynamics.ResidualCoverage.WeightedResidualCoverage

/-- A greedy choice belongs to the pool and maximizes current marginal gain. -/
def IsGreedyChoice
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (pool chosen : Finset Definition) (definition : Definition) : Prop :=
  definition ∈ pool ∧
    ∀ alternative ∈ pool,
      MarginalGain residuals weight separates chosen alternative ≤
        MarginalGain residuals weight separates chosen definition

/-- A one-definition marginal gain cannot exceed the currently uncovered mass. -/
theorem marginalGain_le_uncoveredWeight
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) (definition : Definition) :
    MarginalGain residuals weight separates chosen definition ≤
      UncoveredWeight residuals weight separates chosen := by
  unfold MarginalGain UncoveredWeight
  apply Finset.sum_le_sum
  intro residual inResiduals
  cases covered : CoveredBy separates chosen residual <;>
    cases separated : separates definition residual <;>
      simp

/-- Insertion partitions current uncovered mass into residual mass and new gain. -/
theorem uncoveredWeight_insert_add_marginalGain
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (chosen : Finset Definition) (definition : Definition) :
    UncoveredWeight residuals weight separates (insert definition chosen) +
        MarginalGain residuals weight separates chosen definition =
      UncoveredWeight residuals weight separates chosen := by
  have insertedPartition :=
    weightedGain_add_uncoveredWeight residuals weight separates
      (insert definition chosen)
  have chosenPartition :=
    weightedGain_add_uncoveredWeight residuals weight separates chosen
  have insertion :=
    weightedGain_insert residuals weight separates chosen definition
  omega

/-- A greedy choice maximizes weighted gain after one insertion from the pool. -/
theorem greedy_one_step_optimal
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (pool chosen : Finset Definition) (definition : Definition)
    (greedy :
      IsGreedyChoice residuals weight separates pool chosen definition) :
    ∀ alternative ∈ pool,
      WeightedGain residuals weight separates (insert alternative chosen) ≤
        WeightedGain residuals weight separates (insert definition chosen) := by
  intro alternative inPool
  rw [weightedGain_insert, weightedGain_insert]
  exact Nat.add_le_add_left (greedy.2 alternative inPool) _

/-- Any positive uncovered witness available to the pool forces greedy progress. -/
theorem greedy_positive_progress
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool)
    (pool chosen : Finset Definition) (definition : Definition)
    (greedy :
      IsGreedyChoice residuals weight separates pool chosen definition)
    (progress :
      ∃ alternative ∈ pool, ∃ residual ∈ residuals,
        CoveredBy separates chosen residual = false ∧
          separates alternative residual = true ∧ 0 < weight residual) :
    0 < MarginalGain residuals weight separates chosen definition := by
  rcases progress with
    ⟨alternative, inPool, residual, inResiduals, uncovered, separated, positive⟩
  have positiveAlternative :
      0 < MarginalGain residuals weight separates chosen alternative := by
    unfold MarginalGain
    have termPositive :
        0 < if (!CoveredBy separates chosen residual) &&
            separates alternative residual then
          weight residual
        else 0 := by
      simp [uncovered, separated, positive]
    have termBound :
        (if (!CoveredBy separates chosen residual) &&
              separates alternative residual then
            weight residual
          else 0) ≤
          ∑ candidate ∈ residuals,
            if (!CoveredBy separates chosen candidate) &&
                separates alternative candidate then
              weight candidate
            else 0 := by
      exact Finset.single_le_sum
        (f := fun candidate =>
          if (!CoveredBy separates chosen candidate) &&
              separates alternative candidate then
            weight candidate
          else 0)
        (fun candidate _ => Nat.zero_le _) inResiduals
    exact termPositive.trans_le termBound
  exact lt_of_lt_of_le positiveAlternative (greedy.2 alternative inPool)

/-- Cross-multiplied gain-cost comparison; it reads as gain per cost only when
the compared costs are positive (zero costs satisfy it vacuously). -/
def CostEffectiveChoice
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool) (cost : Definition → Nat)
    (pool chosen : Finset Definition) (definition : Definition) : Prop :=
  definition ∈ pool ∧
    ∀ alternative ∈ pool,
      MarginalGain residuals weight separates chosen alternative * cost definition ≤
        MarginalGain residuals weight separates chosen definition * cost alternative

/-- With one positive uniform cost, cost-effectiveness is exactly greediness. -/
theorem costEffective_of_uniform_cost
    {Definition Residual : Type*} [DecidableEq Definition]
    (residuals : Finset Residual) (weight : Residual → Nat)
    (separates : Definition → Residual → Bool) (cost : Definition → Nat)
    (pool chosen : Finset Definition) (definition : Definition) (c : Nat)
    (uniform : ∀ candidate, cost candidate = c) (positive : 0 < c) :
    CostEffectiveChoice residuals weight separates cost pool chosen definition ↔
      IsGreedyChoice residuals weight separates pool chosen definition := by
  constructor
  · rintro ⟨inPool, comparison⟩
    refine ⟨inPool, ?_⟩
    intro alternative alternativeInPool
    have scaled := comparison alternative alternativeInPool
    rw [uniform definition, uniform alternative] at scaled
    exact Nat.le_of_mul_le_mul_right scaled positive
  · rintro ⟨inPool, comparison⟩
    refine ⟨inPool, ?_⟩
    intro alternative alternativeInPool
    rw [uniform definition, uniform alternative]
    exact Nat.mul_le_mul_right c (comparison alternative alternativeInPool)

#print axioms marginalGain_le_uncoveredWeight
#print axioms uncoveredWeight_insert_add_marginalGain
#print axioms greedy_one_step_optimal
#print axioms greedy_positive_progress
#print axioms costEffective_of_uniform_cost

end D5.S3.ConceptDynamics.ResidualCoverage.GreedyResidualAllocation

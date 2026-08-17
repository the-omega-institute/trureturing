/- GID: D5/S3/Observer/DynamicProgramming/BellmanContraction
   generality: G
   mirror-B: D5/B/S3/Observer/DynamicProgramming/BellmanContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The discounted Bellman operator contracts to the prediction distance. -/

import D5.S3.Observer.MetricGeometry.BellmanMaxEquation
import Mathlib.Topology.MetricSpace.Contracting

/- Library-search audit trail (2026-08-17):
   * Pinned Mathlib and Loogle both found `ContractingWith.fixedPoint_unique'`,
     which supplies uniqueness once the Bellman contraction is established.
   * Loogle found `abs_max_sub_max_le_abs`, used for the pointwise max bound.
   * LeanSearch's `/api/search` endpoint returned HTTP 404.
   * Repository search found the Bellman equation imported above, but no
     contraction or unique-fixed-point theorem for this operator. -/

namespace D5.S3.Observer.DynamicProgramming.BellmanContraction

open D5.S3.Observer.MetricGeometry.BellmanMaxEquation

/-- The one-step discounted Bellman operator on pairwise value functions. -/
def bellmanOperator {Y O : Type*}
    (update : Y -> Y)
    (readout : Y -> O)
    (distance : O -> O -> Real)
    (gamma : NNReal)
    (p : Y -> Y -> Real) : Y -> Y -> Real :=
  fun y y' =>
    max (distance (readout y) (readout y'))
      ((gamma : Real) * p (update y) (update y'))

/-- On a finite nonempty state space, the discounted Bellman operator is a
strict contraction in the uniform norm. Its unique fixed point is the
discounted prediction distance. -/
theorem bellman_operator_contracting_unique_fixed_point
    {Y O : Type*} [Fintype Y] [Nonempty Y]
    (update : Y -> Y)
    (readout : Y -> O)
    (distance : O -> O -> Real)
    (gamma : NNReal)
    (bound : Real)
    (hgamma_pos : 0 < gamma)
    (hgamma_lt_one : gamma < 1)
    (hdistance : forall a b, distance a b ∈ Set.Icc 0 bound) :
    ContractingWith gamma
        (bellmanOperator update readout distance gamma) ∧
      forall p : Y -> Y -> Real,
        Function.IsFixedPt
            (bellmanOperator update readout distance gamma) p ↔
          p = fun y y' =>
            discountedPredictionDistance update readout distance
              (gamma : Real) y y' := by
  have hcontract :
      ContractingWith gamma
        (bellmanOperator update readout distance gamma) := by
    refine ⟨hgamma_lt_one, LipschitzWith.of_dist_le_mul ?_⟩
    intro p q
    apply (dist_pi_le_iff (mul_nonneg gamma.coe_nonneg dist_nonneg)).2
    intro y
    apply (dist_pi_le_iff (mul_nonneg gamma.coe_nonneg dist_nonneg)).2
    intro y'
    simp only [bellmanOperator, Real.dist_eq]
    calc
      |max (distance (readout y) (readout y'))
            ((gamma : Real) * p (update y) (update y')) -
          max (distance (readout y) (readout y'))
            ((gamma : Real) * q (update y) (update y'))| ≤
          |(gamma : Real) * p (update y) (update y') -
            (gamma : Real) * q (update y) (update y')| := by
        simpa only [max_comm] using
          abs_max_sub_max_le_abs
            ((gamma : Real) * p (update y) (update y'))
            ((gamma : Real) * q (update y) (update y'))
            (distance (readout y) (readout y'))
      _ = (gamma : Real) *
          |p (update y) (update y') - q (update y) (update y')| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg gamma.coe_nonneg]
      _ ≤ (gamma : Real) * dist p q := by
        apply mul_le_mul_of_nonneg_left _ gamma.coe_nonneg
        rw [← Real.dist_eq]
        exact
          (dist_le_pi_dist (p (update y)) (q (update y)) (update y')).trans
            (dist_le_pi_dist p q (update y))
  have hgamma_real : (gamma : Real) ∈ Set.Ioc 0 1 := by
    constructor
    · exact_mod_cast hgamma_pos
    · exact_mod_cast hgamma_lt_one.le
  have hprediction_fixed :
      Function.IsFixedPt
        (bellmanOperator update readout distance gamma)
        (fun y y' =>
          discountedPredictionDistance update readout distance
            (gamma : Real) y y') := by
    funext y y'
    exact (discounted_prediction_distance_bellman update readout distance
      (gamma : Real) bound hgamma_real hdistance y y').symm
  refine ⟨hcontract, ?_⟩
  intro p
  constructor
  · intro hp
    exact hcontract.fixedPoint_unique' hp hprediction_fixed
  · intro hp
    simpa only [hp] using hprediction_fixed

#print axioms bellman_operator_contracting_unique_fixed_point

end D5.S3.Observer.DynamicProgramming.BellmanContraction

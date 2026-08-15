/- GID: D5/S3/Observer/MetricGeometry/DiscretePredictionUltrametric
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/DiscretePredictionUltrametric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Discrete-output prediction distance satisfies the strong triangle inequality. -/

import D5.S3.Observer.MetricGeometry.BellmanMaxEquation
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-15):
   * Loogle found `ciSup_sup_eq`, the exact conditionally complete lattice
     identity used to move the pointwise maximum through the discounted
     supremum, and `mul_max_of_nonneg`, the exact pointwise scalar rewrite.
   * LeanSearch returned `IsUltrametricDist.dist_triangle_max`,
     `IsUltrametricDist.mk`, `dist_triangle_max`, and
     `PiNat.dist_triangle_nonarch`. These are generic interfaces or concern a
     fixed half-discount sequence metric, not this arbitrary-discount observer
     distance.
   * The proof imports and applies `ciSup_mono`, `ciSup_sup_eq`,
     `mul_max_of_nonneg`, and `pow_le_one₀`. Repository and formalization-record
     searches found no equal-or-stronger declaration for discrete discounted
     prediction distance.
-/

namespace D5.S3.Observer.MetricGeometry.DiscretePredictionUltrametric

open D5.S3.Observer.MetricGeometry.BellmanMaxEquation

/-- The equality-valued discrepancy on a discrete output type. -/
def discreteOutputDistance {O : Type*} [DecidableEq O] (a b : O) : Real :=
  if a = b then 0 else 1

private theorem discrete_output_distance_mem_Icc
    {O : Type*} [DecidableEq O] (a b : O) :
    discreteOutputDistance a b ∈ Set.Icc (0 : Real) 1 := by
  by_cases h : a = b <;> simp [discreteOutputDistance, h]

private theorem discrete_output_distance_strong_triangle
    {O : Type*} [DecidableEq O] (a b c : O) :
    discreteOutputDistance a c ≤
      max (discreteOutputDistance a b) (discreteOutputDistance b c) := by
  by_cases hac : a = c
  · subst c
    calc
      discreteOutputDistance a a = 0 := by simp [discreteOutputDistance]
      _ ≤ discreteOutputDistance a b :=
        (discrete_output_distance_mem_Icc a b).1
      _ ≤ max (discreteOutputDistance a b) (discreteOutputDistance b a) :=
        le_max_left _ _
  by_cases hab : a = b
  · subst b
    simp [discreteOutputDistance, hac]
  · simp [discreteOutputDistance, hac, hab]

private theorem discounted_discrete_terms_bddAbove
    {Y O : Type*} [DecidableEq O]
    (update : Y -> Y)
    (readout : Y -> O)
    (gamma : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (y y' : Y) :
    BddAbove (Set.range fun k : Nat =>
      gamma ^ k *
        discreteOutputDistance (readout ((update^[k]) y))
          (readout ((update^[k]) y'))) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨k, rfl⟩
  have hdistance :=
    discrete_output_distance_mem_Icc
      (readout ((update^[k]) y)) (readout ((update^[k]) y'))
  calc
    gamma ^ k *
        discreteOutputDistance (readout ((update^[k]) y))
          (readout ((update^[k]) y')) ≤
        1 * discreteOutputDistance (readout ((update^[k]) y))
          (readout ((update^[k]) y')) :=
      mul_le_mul_of_nonneg_right
        (pow_le_one₀ hgamma.1.le hgamma.2) hdistance.1
    _ = discreteOutputDistance (readout ((update^[k]) y))
          (readout ((update^[k]) y')) := one_mul _
    _ ≤ 1 := hdistance.2

/-- With discrete output discrepancy, discounted prediction distance obeys the
strong triangle inequality. Together with the pseudometric laws, this is the
ultrametric law. -/
theorem discounted_prediction_distance_strong_triangle
    {Y O : Type*} [DecidableEq O]
    (update : Y -> Y)
    (readout : Y -> O)
    (gamma : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (y y' z : Y) :
    discountedPredictionDistance update readout discreteOutputDistance gamma y z ≤
      max
        (discountedPredictionDistance update readout discreteOutputDistance gamma y y')
        (discountedPredictionDistance update readout discreteOutputDistance gamma y' z) := by
  have hgamma_nonnegative : 0 ≤ gamma := hgamma.1.le
  have hleft :=
    discounted_discrete_terms_bddAbove update readout gamma hgamma y y'
  have hright :=
    discounted_discrete_terms_bddAbove update readout gamma hgamma y' z
  unfold discountedPredictionDistance
  calc
    (⨆ k : Nat,
        gamma ^ k *
          discreteOutputDistance (readout ((update^[k]) y))
            (readout ((update^[k]) z))) ≤
        ⨆ k : Nat,
          max
            (gamma ^ k *
              discreteOutputDistance (readout ((update^[k]) y))
                (readout ((update^[k]) y')))
            (gamma ^ k *
              discreteOutputDistance (readout ((update^[k]) y'))
                (readout ((update^[k]) z))) := by
      apply ciSup_mono (bbdAbove_range_sup hleft hright)
      intro k
      rw [← mul_max_of_nonneg _ _ (pow_nonneg hgamma_nonnegative k)]
      exact mul_le_mul_of_nonneg_left
        (discrete_output_distance_strong_triangle
          (readout ((update^[k]) y))
          (readout ((update^[k]) y'))
          (readout ((update^[k]) z)))
        (pow_nonneg hgamma_nonnegative k)
    _ = max
        (⨆ k : Nat,
          gamma ^ k *
            discreteOutputDistance (readout ((update^[k]) y))
              (readout ((update^[k]) y')))
        (⨆ k : Nat,
          gamma ^ k *
            discreteOutputDistance (readout ((update^[k]) y'))
              (readout ((update^[k]) z))) :=
      ciSup_sup_eq hleft hright

/-- The theorem's domain and hypotheses are inhabited by a Boolean output
system with discount factor one half. -/
example :
    discountedPredictionDistance id id discreteOutputDistance
        ((1 : Real) / 2) false true ≤
      max
        (discountedPredictionDistance id id discreteOutputDistance
          ((1 : Real) / 2) false false)
        (discountedPredictionDistance id id discreteOutputDistance
          ((1 : Real) / 2) false true) := by
  have hgamma : ((1 : Real) / 2) ∈ Set.Ioc 0 1 := by
    constructor <;> norm_num
  simpa only [id_eq] using
    discounted_prediction_distance_strong_triangle
      (Y := Bool) (O := Bool) id id ((1 : Real) / 2) hgamma false false true

end D5.S3.Observer.MetricGeometry.DiscretePredictionUltrametric

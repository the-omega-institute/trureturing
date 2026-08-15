/- GID: D5/S3/Observer/MetricGeometry/BellmanMaxEquation
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/BellmanMaxEquation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Discounted prediction distance satisfies its one-step Bellman maximum equation. -/

import D5.S3.Observer.MetricGeometry.DiscountedSensorFusion
import Mathlib.Data.Real.Pointwise
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-15):
   * Loogle found `Real.mul_iSup_of_nonneg`, the exact scalar-supremum
     interchange used below, and `sup_iSup_nat_succ` for complete lattices.
     The latter does not apply to the conditionally complete order on `Real`.
   * LeanSearch returned nearby complete-lattice and fixed-point results but no
     full Bellman-equation match.
   * The proof also applies `pow_le_one₀`, `le_ciSup`, and `ciSup_le` from the
     pinned library. Repository and formalization-record searches found no
     equal-or-stronger Bellman declaration.
-/

namespace D5.S3.Observer.MetricGeometry.BellmanMaxEquation

/-- The discounted supremum of output discrepancies along two update orbits. -/
noncomputable def discountedPredictionDistance
    {Y O : Type*}
    (update : Y -> Y)
    (readout : Y -> O)
    (distance : O -> O -> Real)
    (gamma : Real)
    (y y' : Y) : Real :=
  ⨆ k : Nat,
    gamma ^ k *
      distance (readout ((update^[k]) y)) (readout ((update^[k]) y'))

private theorem discounted_terms_bddAbove
    {Y O : Type*}
    (update : Y -> Y)
    (readout : Y -> O)
    (distance : O -> O -> Real)
    (gamma bound : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (hdistance : forall a b, distance a b ∈ Set.Icc 0 bound)
    (y y' : Y) :
    BddAbove (Set.range fun k : Nat =>
      gamma ^ k *
        distance (readout ((update^[k]) y)) (readout ((update^[k]) y'))) := by
  refine ⟨bound, ?_⟩
  rintro _ ⟨k, rfl⟩
  calc
    gamma ^ k *
        distance (readout ((update^[k]) y)) (readout ((update^[k]) y')) ≤
        1 * distance (readout ((update^[k]) y)) (readout ((update^[k]) y')) :=
      mul_le_mul_of_nonneg_right
        (pow_le_one₀ hgamma.1.le hgamma.2)
        (hdistance _ _).1
    _ = distance (readout ((update^[k]) y)) (readout ((update^[k]) y')) :=
      one_mul _
    _ ≤ bound := (hdistance _ _).2

/-- Discounted prediction distance is the maximum of the current discrepancy
and the discounted prediction distance after one update. -/
theorem discounted_prediction_distance_bellman
    {Y O : Type*}
    (update : Y -> Y)
    (readout : Y -> O)
    (distance : O -> O -> Real)
    (gamma bound : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (hdistance : forall a b, distance a b ∈ Set.Icc 0 bound)
    (y y' : Y) :
    discountedPredictionDistance update readout distance gamma y y' =
      max (distance (readout y) (readout y'))
        (gamma * discountedPredictionDistance update readout distance gamma
          (update y) (update y')) := by
  have hgamma_nonnegative : 0 ≤ gamma := hgamma.1.le
  have hcurrent :=
    discounted_terms_bddAbove update readout distance gamma bound
      hgamma hdistance y y'
  have hnext :=
    discounted_terms_bddAbove update readout distance gamma bound
      hgamma hdistance (update y) (update y')
  unfold discountedPredictionDistance
  apply le_antisymm
  · apply ciSup_le
    intro k
    cases k with
    | zero =>
        simpa only [pow_zero, Function.iterate_zero_apply, one_mul] using
          (le_max_left (distance (readout y) (readout y'))
            (gamma * ⨆ k : Nat,
              gamma ^ k *
                distance (readout ((update^[k]) (update y)))
                  (readout ((update^[k]) (update y')))))
    | succ k =>
        calc
          gamma ^ k.succ *
              distance (readout ((update^[k.succ]) y))
                (readout ((update^[k.succ]) y')) =
              gamma *
                (gamma ^ k *
                  distance (readout ((update^[k]) (update y)))
                    (readout ((update^[k]) (update y')))) := by
            simp only [pow_succ', Function.iterate_succ_apply, mul_assoc]
          _ ≤ gamma *
              (⨆ j : Nat,
                gamma ^ j *
                  distance (readout ((update^[j]) (update y)))
                    (readout ((update^[j]) (update y')))) :=
            mul_le_mul_of_nonneg_left (le_ciSup hnext k) hgamma_nonnegative
          _ ≤ max (distance (readout y) (readout y'))
              (gamma *
                (⨆ j : Nat,
                  gamma ^ j *
                    distance (readout ((update^[j]) (update y)))
                      (readout ((update^[j]) (update y'))))) :=
            le_max_right _ _
  · apply max_le
    · simpa only [pow_zero, Function.iterate_zero_apply, one_mul] using
        (le_ciSup hcurrent 0)
    · rw [Real.mul_iSup_of_nonneg hgamma_nonnegative]
      apply ciSup_le
      intro k
      calc
        gamma *
            (gamma ^ k *
              distance (readout ((update^[k]) (update y)))
                (readout ((update^[k]) (update y')))) =
            gamma ^ k.succ *
              distance (readout ((update^[k.succ]) y))
                (readout ((update^[k.succ]) y')) := by
          simp only [pow_succ', Function.iterate_succ_apply, mul_assoc]
        _ ≤ ⨆ j : Nat,
            gamma ^ j *
              distance (readout ((update^[j]) y))
                (readout ((update^[j]) y')) :=
          le_ciSup hcurrent k.succ

/-- The theorem's domain and hypotheses are inhabited by a one-state system
with a constant unit discrepancy and discount factor one half. -/
example :
    discountedPredictionDistance id (fun _ : Unit => ())
        (fun _ _ => (1 : Real)) ((1 : Real) / 2) () () =
      max 1 (((1 : Real) / 2) *
        discountedPredictionDistance id (fun _ : Unit => ())
          (fun _ _ => (1 : Real)) ((1 : Real) / 2) () ()) := by
  have hgamma : ((1 : Real) / 2) ∈ Set.Ioc 0 1 := by
    constructor <;> norm_num
  have hdistance : forall _ _ : Unit, (1 : Real) ∈ Set.Icc 0 1 := by
    intro _ _
    exact ⟨zero_le_one, le_rfl⟩
  simpa only [id_eq] using
    discounted_prediction_distance_bellman
      (Y := Unit) (O := Unit)
      id (fun _ => ()) (fun _ _ => (1 : Real))
      ((1 : Real) / 2) 1 hgamma hdistance () ()

end D5.S3.Observer.MetricGeometry.BellmanMaxEquation

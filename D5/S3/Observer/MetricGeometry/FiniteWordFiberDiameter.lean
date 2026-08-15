/- GID: D5/S3/Observer/MetricGeometry/FiniteWordFiberDiameter
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/FiniteWordFiberDiameter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A shared finite readout prefix gives a geometric prediction-distance bound. -/

import D5.S3.Observer.MetricGeometry.BellmanMaxEquation
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-15):
   * Loogle and LeanSearch returned no full theorem matching the finite-prefix
     diameter bound.
   * The proof imports and applies the exact support hits `ciSup_le` and
     `pow_le_pow_of_le_one`; repository and digestion searches found no duplicate. -/

namespace D5.S3.Observer.MetricGeometry.FiniteWordFiberDiameter

open BellmanMaxEquation

/-- States whose first `m + 1` readouts agree have discounted prediction
distance at most the remaining geometric scale times the global diameter. -/
theorem finite_word_fiber_prediction_diameter
    {Y O : Type*}
    (update : Y -> Y)
    (readout : Y -> O)
    (distance : O -> O -> Real)
    (gamma bound : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (hself : forall a : O, distance a a = 0)
    (hdistance : forall a b : O, distance a b ≤ bound)
    (m : Nat) (y y' : Y)
    (hprefix : ∀ k ≤ m,
      readout ((update^[k]) y) = readout ((update^[k]) y')) :
    discountedPredictionDistance update readout distance gamma y y' ≤
      gamma ^ (m + 1) * bound := by
  have hbound_nonnegative : 0 ≤ bound := by
    calc
      0 = distance (readout y) (readout y) := (hself _).symm
      _ ≤ bound := hdistance _ _
  unfold discountedPredictionDistance
  apply ciSup_le
  intro k
  by_cases hk : k ≤ m
  · rw [hprefix k hk, hself, mul_zero]
    exact mul_nonneg (pow_nonneg hgamma.1.le _) hbound_nonnegative
  · have hmk : m + 1 ≤ k := by
      omega
    calc
      gamma ^ k *
          distance (readout ((update^[k]) y)) (readout ((update^[k]) y')) ≤
          gamma ^ k * bound :=
        mul_le_mul_of_nonneg_left (hdistance _ _) (pow_nonneg hgamma.1.le _)
      _ ≤ gamma ^ (m + 1) * bound :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hgamma.1.le hgamma.2 hmk)
          hbound_nonnegative

-- A one-state system witnesses that the statement and hypotheses are inhabited.
example (m : Nat) :
    discountedPredictionDistance id (fun _ : Unit => ()) (fun _ _ => 0)
        ((1 : Real) / 2) () () ≤
      ((1 : Real) / 2) ^ (m + 1) * 0 := by
  apply finite_word_fiber_prediction_diameter
      (update := id) (readout := fun _ : Unit => ()) (distance := fun _ _ => 0)
      (gamma := (1 : Real) / 2) (bound := 0) (m := m)
  · constructor <;> norm_num
  · intro a
    rfl
  · intro a b
    exact le_rfl
  · intro k hk
    rfl

end D5.S3.Observer.MetricGeometry.FiniteWordFiberDiameter

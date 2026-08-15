/- GID: D5/S3/Observer/MetricGeometry/DiscountedSensorFusion
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/DiscountedSensorFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Discounted sensor-fusion distance is the maximum of its component distances. -/

import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-15):
   * Loogle found `ciSup_sup_eq`, the exact conditionally complete lattice
     identity used below, and `mul_max_of_nonneg`, the pointwise rewrite.
   * The supporting power bound is the imported theorem `pow_le_one₀`.
   * LeanSearch returned nearby supremum results but no full-statement match;
     repository and formalization-record searches also found no duplicate.
-/

namespace D5.S3.Observer.MetricGeometry.DiscountedSensorFusion

/-- For two bounded component discrepancies, the discounted distance formed
with their pointwise maximum is the maximum of the component discounted
distances. -/
theorem discounted_sensor_fusion_distance_eq_max
    {Y O1 O2 : Type*}
    (update : Y -> Y)
    (readout1 : Y -> O1)
    (readout2 : Y -> O2)
    (distance1 : O1 -> O1 -> Real)
    (distance2 : O2 -> O2 -> Real)
    (gamma bound1 bound2 : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (hdistance1 : forall a b, distance1 a b ∈ Set.Icc 0 bound1)
    (hdistance2 : forall a b, distance2 a b ∈ Set.Icc 0 bound2)
    (y y' : Y) :
    (⨆ k : Nat,
        gamma ^ k *
          max
            (distance1 (readout1 ((update^[k]) y))
              (readout1 ((update^[k]) y')))
            (distance2 (readout2 ((update^[k]) y))
              (readout2 ((update^[k]) y')))) =
      max
        (⨆ k : Nat,
          gamma ^ k *
            distance1 (readout1 ((update^[k]) y))
              (readout1 ((update^[k]) y')))
        (⨆ k : Nat,
          gamma ^ k *
            distance2 (readout2 ((update^[k]) y))
              (readout2 ((update^[k]) y'))) := by
  have hgamma_nonnegative : 0 ≤ gamma := hgamma.1.le
  have hdiscounted1 : BddAbove (Set.range fun k : Nat =>
      gamma ^ k *
        distance1 (readout1 ((update^[k]) y))
          (readout1 ((update^[k]) y'))) := by
    refine ⟨bound1, ?_⟩
    rintro _ ⟨k, rfl⟩
    calc
      gamma ^ k *
          distance1 (readout1 ((update^[k]) y))
            (readout1 ((update^[k]) y')) ≤
          1 * distance1 (readout1 ((update^[k]) y))
            (readout1 ((update^[k]) y')) :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ hgamma_nonnegative hgamma.2)
          (hdistance1 _ _).1
      _ = distance1 (readout1 ((update^[k]) y))
            (readout1 ((update^[k]) y')) := one_mul _
      _ ≤ bound1 := (hdistance1 _ _).2
  have hdiscounted2 : BddAbove (Set.range fun k : Nat =>
      gamma ^ k *
        distance2 (readout2 ((update^[k]) y))
          (readout2 ((update^[k]) y'))) := by
    refine ⟨bound2, ?_⟩
    rintro _ ⟨k, rfl⟩
    calc
      gamma ^ k *
          distance2 (readout2 ((update^[k]) y))
            (readout2 ((update^[k]) y')) ≤
          1 * distance2 (readout2 ((update^[k]) y))
            (readout2 ((update^[k]) y')) :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ hgamma_nonnegative hgamma.2)
          (hdistance2 _ _).1
      _ = distance2 (readout2 ((update^[k]) y))
            (readout2 ((update^[k]) y')) := one_mul _
      _ ≤ bound2 := (hdistance2 _ _).2
  simp_rw [mul_max_of_nonneg _ _ (pow_nonneg hgamma_nonnegative _)]
  exact ciSup_sup_eq hdiscounted1 hdiscounted2

/-- The hypotheses are inhabited by a half-discounted two-sensor system with
one nonzero component discrepancy. -/
example :
    (⨆ k : Nat, ((1 : Real) / 2) ^ k * max 1 0) =
      max (⨆ k : Nat, ((1 : Real) / 2) ^ k * 1)
        (⨆ k : Nat, ((1 : Real) / 2) ^ k * 0) := by
  have hgamma : ((1 : Real) / 2) ∈ Set.Ioc 0 1 := by
    constructor <;> norm_num
  have hone : forall _ _ : Unit, (1 : Real) ∈ Set.Icc 0 1 := by
    intro _ _
    exact ⟨zero_le_one, le_rfl⟩
  have hzero : forall _ _ : Unit, (0 : Real) ∈ Set.Icc 0 0 := by
    intro _ _
    exact ⟨le_rfl, le_rfl⟩
  simpa only [Function.iterate_id] using
    discounted_sensor_fusion_distance_eq_max
      (Y := Unit) (O1 := Unit) (O2 := Unit)
      id (fun _ => ()) (fun _ => ())
      (fun _ _ => 1) (fun _ _ => 0)
      ((1 : Real) / 2) 1 0 hgamma hone hzero () ()

end D5.S3.Observer.MetricGeometry.DiscountedSensorFusion

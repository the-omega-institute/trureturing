/- GID: D5/S3/Observer/MetricGeometry/OutputTrajectoryError
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/OutputTrajectoryError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound output-orbit error by readout mismatch and accumulated transition defect. -/

import Mathlib.Topology.MetricSpace.Lipschitz

open scoped BigOperators

/- Library-search audit trail (2026-08-15):
   * Loogle queries for `LipschitzWith _ _` found the exact supporting results
     `LipschitzWith.iterate` and `LipschitzWith.edist_le_mul_of_le`; both are
     imported and applied below.
   * Loogle found no theorem matching the full approximate-semiconjugacy
     output-orbit estimate with a finite geometric sum.
   * LeanSearch API queries returned no usable full-statement result, and
     repository searches found no declaration with this conclusion.
-/

namespace D5.S3.Observer.MetricGeometry.OutputTrajectoryError

/-- A uniform one-step transition defect accumulates as a finite geometric
sum, while the current readout mismatch contributes one additive error. -/
theorem output_trajectory_error
    {Y Z O : Type*} [PseudoEMetricSpace Z] [PseudoEMetricSpace O]
    (tau : Y -> Y) (sigma : Z -> Z) (pi : Y -> Z)
    (q : Y -> O) (o : Z -> O)
    (L M : NNReal) (delta eta : ENNReal)
    (hsigma : LipschitzWith L sigma) (ho : LipschitzWith M o)
    (hdefect : forall y, edist (pi (tau y)) (sigma (pi y)) <= delta)
    (hreadout : forall y, edist (q y) (o (pi y)) <= eta) :
    forall (k : Nat) (y : Y),
      edist (q ((tau^[k]) y)) (o ((sigma^[k]) (pi y))) <=
        eta + (M : ENNReal) * delta *
          ∑ j ∈ Finset.range k, (L : ENNReal) ^ j := by
  have hOrbit : forall (k : Nat) (y : Y),
      edist (pi ((tau^[k]) y)) ((sigma^[k]) (pi y)) <=
        delta * ∑ j ∈ Finset.range k, (L : ENNReal) ^ j := by
    intro k
    induction k with
    | zero =>
        intro y
        simp
    | succ k ih =>
        intro y
        have hStep :=
          (hsigma.iterate k).edist_le_mul_of_le (hdefect y)
        calc
          edist (pi ((tau^[Nat.succ k]) y))
              ((sigma^[Nat.succ k]) (pi y)) =
            edist (pi ((tau^[k]) (tau y)))
              ((sigma^[k]) (sigma (pi y))) := by
                rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
          _ <= edist (pi ((tau^[k]) (tau y)))
                ((sigma^[k]) (pi (tau y))) +
              edist ((sigma^[k]) (pi (tau y)))
                ((sigma^[k]) (sigma (pi y))) := edist_triangle _ _ _
          _ <= delta * ∑ j ∈ Finset.range k, (L : ENNReal) ^ j +
                (L : ENNReal) ^ k * delta := by
              apply add_le_add (ih (tau y))
              simpa only [ENNReal.coe_pow] using hStep
          _ = delta * ∑ j ∈ Finset.range (Nat.succ k),
                (L : ENNReal) ^ j := by
              rw [Finset.sum_range_succ, mul_add]
              ac_rfl
  intro k y
  calc
    edist (q ((tau^[k]) y)) (o ((sigma^[k]) (pi y))) <=
        edist (q ((tau^[k]) y)) (o (pi ((tau^[k]) y))) +
          edist (o (pi ((tau^[k]) y)))
            (o ((sigma^[k]) (pi y))) := edist_triangle _ _ _
    _ <= eta + (M : ENNReal) *
          edist (pi ((tau^[k]) y)) ((sigma^[k]) (pi y)) :=
      add_le_add (hreadout ((tau^[k]) y)) (ho.edist_le_mul _ _)
    _ <= eta + (M : ENNReal) *
          (delta * ∑ j ∈ Finset.range k, (L : ENNReal) ^ j) :=
      add_le_add le_rfl (mul_le_mul_right (hOrbit k y) _)
    _ = eta + (M : ENNReal) * delta *
          ∑ j ∈ Finset.range k, (L : ENNReal) ^ j := by
      rw [mul_assoc]

/-- A two-state system with a flipping concrete update and a stationary
abstract update satisfies the assumptions with unit transition defect. -/
example :
    forall (k : Nat) (y : Bool),
      edist
          ((fun b : Bool => if b then (1 : Real) else 0)
            (((fun b : Bool => !b)^[k]) y))
          ((fun b : Bool => if b then (1 : Real) else 0) y) <=
        ∑ j ∈ Finset.range k, (1 : ENNReal) ^ j := by
  let embed : Bool -> Real := fun b => if b then 1 else 0
  simpa [embed] using
    output_trajectory_error (Y := Bool) (Z := Real) (O := Real)
      (fun b : Bool => !b) id embed embed id 1 1 1 0
      LipschitzWith.id LipschitzWith.id
      (by intro y; cases y <;> simp [embed, edist_dist, Real.dist_eq])
      (by intro y; simp)

end D5.S3.Observer.MetricGeometry.OutputTrajectoryError

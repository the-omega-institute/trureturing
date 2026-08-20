/- GID: D5/S3/ObserverMemory/InverseLimits/FiniteBilateralTrajectory
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/FiniteBilateralTrajectory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bilateral trajectories of a finite system are uniquely based at periodic points. -/

import D5.S3.ObserverMemory.InverseLimits.BackwardOrbitCore

/- Library-search audit trail (2026-08-20):
   * The repository exact hit `backward_orbit_coordinate_periodic` proves that
     every state of every backward-compatible trajectory is periodic; it is
     applied directly below.
   * The repository exact hit `backward_orbit_eval_zero_bijective` identifies
     trajectories uniquely by their periodic coordinate-zero state; it is
     applied directly below.
   * Those exact results apply pinned-Mathlib declarations
     `Function.bijOn_periodicPts`, `Function.IsPeriodicPt.eq_of_apply_eq`, and
     `Fintype.exists_ne_map_eq_of_card_lt`.
   * Repository and pinned-Mathlib shape searches found no theorem packaging
     both public clauses below. -/

namespace D5.S3.ObserverMemory.InverseLimits.FiniteBilateralTrajectory

open D5.S3.ObserverMemory.InverseLimits.BackwardOrbitCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A bilateral periodic trajectory is represented by its compatible backward
half; every represented state is required to be a periodic point. The forward
half is generated uniquely by the update. -/
def BilateralPeriodicTrajectory {Y : Type*} (update : Y -> Y) :=
  {orbit : BackwardOrbit update //
    ∀ n, orbit.1 n ∈ Function.periodicPts update}

/-- On a finite carrier, every state in every bilateral trajectory is
periodic. Conversely, each periodic point is coordinate zero of a unique
bilateral periodic trajectory. -/
theorem finite_bilateral_trajectory {Y : Type*} [Finite Y]
    (update : Y -> Y) :
    (∀ orbit : BackwardOrbit update, ∀ n,
      orbit.1 n ∈ Function.periodicPts update) ∧
      (∀ point : {y : Y // y ∈ Function.periodicPts update},
        ∃! trajectory : BilateralPeriodicTrajectory update,
          trajectory.1.1 0 = point.1) := by
  have evaluationBijective := backward_orbit_eval_zero_bijective update
  constructor
  · intro orbit n
    exact backward_orbit_coordinate_periodic orbit n
  · intro point
    rcases evaluationBijective.2 point with ⟨orbit, horbit⟩
    let trajectory : BilateralPeriodicTrajectory update :=
      ⟨orbit, fun n => backward_orbit_coordinate_periodic orbit n⟩
    refine ⟨trajectory, ?_, ?_⟩
    · exact congrArg Subtype.val horbit
    · intro other hother
      apply Subtype.ext
      apply evaluationBijective.1
      apply Subtype.ext
      simpa [trajectory] using
        hother.trans (congrArg Subtype.val horbit).symm

/-- A singleton finite system witnesses the quantified carrier and trajectory
domains. -/
example :
    ∀ orbit : BackwardOrbit (id : Unit -> Unit), ∀ n,
      orbit.1 n ∈ Function.periodicPts (id : Unit -> Unit) :=
  (finite_bilateral_trajectory (id : Unit -> Unit)).1

#print axioms finite_bilateral_trajectory

end D5.S3.ObserverMemory.InverseLimits.FiniteBilateralTrajectory

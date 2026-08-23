/- GID: D5/S3/ObserverMemory/FiniteCountermodels/CanonicalPathBranchNoncommutation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FiniteCountermodels/CanonicalPathBranchNoncommutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Backward paths forget canonical transient-child branch multiplicities. -/

import D5.S1.FixedPoints.RootedTransientTreeClassification
import D5.S3.ObserverMemory.FiniteCountermodels.PathBranchNoncommutation

/- Library-search audit trail (2026-08-23):
   * Exact repository hits `pastCoreEquiv` and `backward_orbit_eval_zero_bijective`
     identify backward paths with their periodic cores.
   * Exact family hit `RootedTransientTreeClassification.TransientChild` is the
     canonical nonperiodic-child predicate and is used directly in every child carrier.
   * The frozen predecessor supplies the finite countermodel and all eleven clauses;
     no corrected theorem with the canonical child predicate was already present.
   * Pinned Mathlib periodic-point and finite-cardinality searches found no theorem
     packaging the periodic-core path equivalence with a branch-sensitive countermodel. -/

namespace D5.S3.ObserverMemory.FiniteCountermodels.CanonicalPathBranchNoncommutation

open D5.S3.ObserverMemory.InverseLimits.BackwardOrbitCore
open D5.S3.ObserverMemory.InverseLimits.IdentityFuturePastGap
open D5.S3.ObserverMemory.FiniteCountermodels.PathBranchNoncommutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Ordinary backward paths are determined by periodic-core dynamics, while the
canonical transient-child predicate distinguishes complete incoming branch trees. -/
theorem path_limit_branch_noncommutation_ssot :
    (forall {Y Z : Type*} [Finite Y] [Finite Z]
      (tau : Y -> Y) (sigma : Z -> Z)
      (coreEquiv : PeriodicCore tau ≃ PeriodicCore sigma)
      (orbit : BackwardOrbit tau),
      (backwardOrbitEquivOfPeriodicCoreEquiv tau sigma coreEquiv orbit).1 0 =
        (coreEquiv (pastCoreEquiv tau orbit)).1) /\
    (exists child : Fin 2, child ∉ Function.periodicPts oneBranchMap) /\
    (exists child : Fin 3, child ∉ Function.periodicPts twoBranchMap) /\
    (forall point : PeriodicCore oneBranchMap,
      countermodelCoreEquiv
          ⟨oneBranchMap point.1,
            (Function.bijOn_periodicPts oneBranchMap).mapsTo point.2⟩ =
        ⟨twoBranchMap (countermodelCoreEquiv point).1,
          (Function.bijOn_periodicPts twoBranchMap).mapsTo
            (countermodelCoreEquiv point).2⟩) /\
    (forall orbit : BackwardOrbit oneBranchMap,
      (backwardOrbitEquivOfPeriodicCoreEquiv oneBranchMap twoBranchMap
          countermodelCoreEquiv orbit).1 0 =
        (countermodelCoreEquiv (pastCoreEquiv oneBranchMap orbit)).1) /\
    (forall child : Fin 2, child ∉ Function.periodicPts oneBranchMap ->
      IsEmpty {predecessor : Fin 2 //
        D5.S1.FixedPoints.RootedTransientTreeClassification.TransientChild
          oneBranchMap predecessor child}) /\
    (forall child : Fin 3, child ∉ Function.periodicPts twoBranchMap ->
      IsEmpty {predecessor : Fin 3 //
        D5.S1.FixedPoints.RootedTransientTreeClassification.TransientChild
          twoBranchMap predecessor child}) /\
    Nat.card {child : Fin 2 //
      D5.S1.FixedPoints.RootedTransientTreeClassification.TransientChild
        oneBranchMap child 0} = 1 /\
    Nat.card {child : Fin 3 //
      D5.S1.FixedPoints.RootedTransientTreeClassification.TransientChild
        twoBranchMap child 0} = 2 /\
    Nat.card {child : Fin 2 //
      D5.S1.FixedPoints.RootedTransientTreeClassification.TransientChild
        oneBranchMap child 0} ≠
      Nat.card {child : Fin 3 //
        D5.S1.FixedPoints.RootedTransientTreeClassification.TransientChild
          twoBranchMap child 0} /\
    Not (exists relabel : Fin 2 ≃ Fin 3,
      Function.Semiconj relabel oneBranchMap twoBranchMap) := by
  simpa only [
    D5.S3.ObserverMemory.FiniteCountermodels.PathBranchNoncommutation.TransientChild,
    D5.S1.FixedPoints.RootedTransientTreeClassification.TransientChild] using
    path_limit_branch_noncommutation

#print axioms path_limit_branch_noncommutation_ssot

end D5.S3.ObserverMemory.FiniteCountermodels.CanonicalPathBranchNoncommutation

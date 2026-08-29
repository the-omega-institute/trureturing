/- GID: D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite-horizon behavior kernels descend by one new coordinate, intersect to the complete kernel, and stabilize at the finite completion depth. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-29):
   * The canonical finite and complete readouts are `futureReadoutWord` and
     `completeItinerary`; the canonical finite stopping bound is `completionDepth`.
   * Pinned Mathlib supplies `Fin.lastCases`, setoid infima, and function extensionality.
   * No second behavior-completion carrier is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.RefinementClosure.FiniteHorizonKernelRecurrence

open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

universe u v

/-- Equality through update times zero through `m`. -/
abbrev finiteHorizonKernel
    {Y : Type u} {O : Type v}
    (tau : Y -> Y) (q : Y -> O) (m : Nat) : Setoid Y :=
  Setoid.ker (futureReadoutWord tau q m)

/-- Adding one horizon coordinate intersects the previous kernel with equality
of the new terminal observation. -/
theorem finite_horizon_kernel_succ_iff
    {Y : Type u} {O : Type v}
    (tau : Y -> Y) (q : Y -> O) (m : Nat) (y y' : Y) :
    finiteHorizonKernel tau q (m + 1) y y' <->
      finiteHorizonKernel tau q m y y' ∧
        q ((tau^[m + 1]) y) = q ((tau^[m + 1]) y') := by
  constructor
  · intro sameLongWord
    constructor
    · funext k
      exact congrFun sameLongWord k.castSucc
    · exact congrFun sameLongWord (Fin.last (m + 1))
  · rintro ⟨samePrefix, sameLast⟩
    funext k
    refine Fin.lastCases ?_ (fun j : Fin (m + 1) => ?_) k
    · exact sameLast
    · exact congrFun samePrefix j

/-- Longer observation horizons yield finer kernels. -/
theorem finite_horizon_kernel_antitone
    {Y : Type u} {O : Type v}
    (tau : Y -> Y) (q : Y -> O) {m n : Nat} (hmn : m <= n) :
    finiteHorizonKernel tau q n <= finiteHorizonKernel tau q m := by
  intro y y' sameLongWord
  funext k
  exact congrFun sameLongWord
    ⟨k, lt_of_lt_of_le k.isLt (Nat.succ_le_succ hmn)⟩

/-- The complete behavior kernel is the infimum of all finite-horizon kernels. -/
theorem complete_kernel_eq_iInf_finite_horizon
    {Y : Type u} {O : Type v}
    (tau : Y -> Y) (q : Y -> O) :
    Setoid.ker (completeItinerary tau q) =
      ⨅ m, finiteHorizonKernel tau q m := by
  apply le_antisymm
  · intro y y' sameComplete m
    funext k
    exact congrFun sameComplete k
  · intro y y' sameAtEveryDepth
    funext n
    exact congrFun (sameAtEveryDepth n) ⟨n, Nat.lt_succ_self n⟩

/-- A first separating terminal coordinate certifies strict refinement at the
next finite horizon. -/
theorem finite_horizon_first_new_coordinate_strict
    {Y : Type u} {O : Type v}
    (tau : Y -> Y) (q : Y -> O) (m : Nat) (y y' : Y)
    (samePrefix : finiteHorizonKernel tau q m y y')
    (newCoordinateSeparates :
      q ((tau^[m + 1]) y) ≠ q ((tau^[m + 1]) y')) :
    finiteHorizonKernel tau q (m + 1) < finiteHorizonKernel tau q m := by
  constructor
  · exact finite_horizon_kernel_antitone tau q (Nat.le_succ m)
  · intro reverseInclusion
    have sameLongWord := reverseInclusion samePrefix
    exact newCoordinateSeparates
      ((finite_horizon_kernel_succ_iff tau q m y y').1 sameLongWord).2

/-- On a finite state space, the canonical completion depth already has the
complete infinite-horizon kernel. -/
theorem finite_horizon_stabilizes_at_completionDepth
    {Y : Type u} {O : Type v} [Fintype Y]
    (tau : Y -> Y) (q : Y -> O) :
    finiteHorizonKernel tau q (completionDepth tau q) =
      Setoid.ker (completeItinerary tau q) := by
  apply le_antisymm
  · intro y y' samePrefix
    exact completion_depth_determines_itinerary tau q y y' samePrefix
  · intro y y' sameComplete
    funext k
    exact congrFun sameComplete k

/-- The identity readout stabilizes already at depth zero. -/
example :
    finiteHorizonKernel id (fun x : Bool => x) 0 =
      Setoid.ker (completeItinerary id (fun x : Bool => x)) := by
  apply le_antisymm
  · intro x y sameZero
    funext n
    simpa [futureReadoutWord, completeItinerary] using congrFun sameZero 0
  · intro x y sameComplete
    funext k
    exact congrFun sameComplete k

#print axioms finite_horizon_kernel_succ_iff
#print axioms complete_kernel_eq_iInf_finite_horizon
#print axioms finite_horizon_stabilizes_at_completionDepth

end D5.S3.ObserverMemory.RefinementClosure.FiniteHorizonKernelRecurrence

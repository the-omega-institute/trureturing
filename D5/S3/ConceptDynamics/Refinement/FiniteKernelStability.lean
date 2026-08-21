/- GID: D5/S3/ConceptDynamics/Refinement/FiniteKernelStability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/FiniteKernelStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite predictive kernel chains stabilize within their class-count budget. -/

import D5.S3.Observer.Separation.FiniteObservationRefinementBound

/- Library-search audit trail (2026-08-21):
   * Repository searches for `finite.*stabilize`, `kernel.*chain`, `Setoid`, and
     `Quotient.*card` found the exact theorem
     `finite_observation_refinement_and_stability_bound`; it is imported and applied below.
   * Repository search also found the exact permanence theorem
     `prediction_partition_stable_forever`; it is applied to upgrade one stable step to all
     later depths.
   * Pinned Mathlib searches for `finite.*Setoid`, `Setoid.*finite`, and
     `Fintype.card.*Quotient` found the quotient-cardinality infrastructure used by the imported
     theorem, including `Setoid.quotientKerEquivOfSurjective`, `Equiv.funUnique`,
     `Fintype.card_quotient_le`, and `Fintype.card_le_of_surjective`.
   * The brief records that local Loogle and LeanSearch executables are unavailable, so they were
     not invoked and no absence claim relies on them. -/

noncomputable section

namespace D5.S3.ConceptDynamics.Refinement.FiniteKernelStability

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.PredictionPartitionStability

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The kernel relation obtained from prediction words through depth `m`. -/
abbrev kernelAt {X O : Type*} (update : X -> X) (readout : X -> O) (m : Nat) : Setoid X :=
  observationSetoid update readout m

/-- The number of prediction classes visible through depth `m`. -/
abbrev classCount {X O : Type*} [Fintype X]
    (update : X -> X) (readout : X -> O) (m : Nat) : Nat :=
  observationClassCount update readout m

/-- On a finite state space, predictive kernels form a decreasing chain that becomes permanently
stable. Every depth before the least stable depth is a strict refinement, its number is bounded by
the gained class count, and infinite-future equivalence is already decided at that finite depth. -/
theorem finite_kernel_chain_stability
    {X O : Type*} [Fintype X] [Fintype O] [Nonempty X]
    (update : X -> X) (readout : X -> O)
    (hreadout : Function.Surjective readout) :
    let stableDepth := observationStabilityDepth update readout
    (forall m, kernelAt update readout (m + 1) <= kernelAt update readout m) /\
      kernelAt update readout stableDepth = kernelAt update readout (stableDepth + 1) /\
      (forall r, kernelAt update readout (stableDepth + r) =
        kernelAt update readout stableDepth) /\
      (forall m, m < stableDepth ->
        kernelAt update readout (m + 1) ≠ kernelAt update readout m) /\
      classCount update readout 0 = Fintype.card O /\
      stableDepth <= classCount update readout stableDepth - classCount update readout 0 /\
      classCount update readout stableDepth - classCount update readout 0 <=
        Fintype.card X - classCount update readout 0 /\
      (forall x y, kernelAt update readout stableDepth x y <->
        forall k, observedAt update readout k x = observedAt update readout k y) := by
  dsimp only
  rcases finite_observation_refinement_and_stability_bound update readout hreadout with
    ⟨hchain, _hcountMono, ⟨hstable, hminimal⟩, hdepthBound, hclassBound⟩
  let stableDepth := observationStabilityDepth update readout
  have hwordStep : forall x y,
      futureReadoutWord update readout stableDepth x =
          futureReadoutWord update readout stableDepth y <->
        futureReadoutWord update readout (stableDepth + 1) x =
          futureReadoutWord update readout (stableDepth + 1) y := by
    intro x y
    change
      observationSetoid update readout (observationStabilityDepth update readout) x y <->
        observationSetoid update readout
          (observationStabilityDepth update readout + 1) x y
    rw [hstable]
  have hforever :=
    prediction_partition_stable_forever update readout stableDepth hwordStep
  have hwordSurjective : Function.Surjective (futureReadoutWord update readout 0) := by
    intro word
    rcases hreadout (word 0) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    funext k
    have hk : k = (0 : Fin 1) := Fin.eq_zero k
    subst k
    simpa [futureReadoutWord] using hx
  have hinitial : classCount update readout 0 = Fintype.card O := by
    change Fintype.card
      (Quotient (Setoid.ker (futureReadoutWord update readout 0))) = Fintype.card O
    exact Fintype.card_congr
      ((Setoid.quotientKerEquivOfSurjective
        (futureReadoutWord update readout 0) hwordSurjective).trans
          (Equiv.funUnique (Fin 1) O))
  have hclassBound' :
      classCount update readout stableDepth - classCount update readout 0 <=
        Fintype.card X - classCount update readout 0 := by
    simpa only [hinitial] using hclassBound
  refine ⟨hchain, hstable, ?_, ?_, hinitial, hdepthBound, hclassBound', ?_⟩
  · intro r
    apply Setoid.ext
    intro x y
    exact hforever.2 r x y
  · intro m hm hEq
    exact (Nat.not_le_of_lt hm) (hminimal m hEq.symm)
  · intro x y
    constructor
    · intro hfinite k
      have hlong := (hforever.2 k x y).2 hfinite
      exact congrFun hlong
        (show Fin (stableDepth + k + 1) from ⟨k, by omega⟩)
    · intro hinfinite
      funext k
      exact hinfinite k.val

/-- The hypotheses and conclusion have a concrete finite nontrivial instance. -/
example := finite_kernel_chain_stability
  (id : Bool -> Bool) (id : Bool -> Bool) Function.surjective_id

#print axioms finite_kernel_chain_stability

end D5.S3.ConceptDynamics.Refinement.FiniteKernelStability

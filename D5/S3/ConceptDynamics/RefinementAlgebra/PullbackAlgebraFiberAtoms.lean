/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/PullbackAlgebraFiberAtoms
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/PullbackAlgebraFiberAtoms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Minimal nonempty pullback events are exactly the realized readout fibers. -/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-26):
   * Body-shape search `{observable | Function.FactorsThrough observable q}`
     found the canonical `PullbackAlgebra` owner in
     `Dialectics.DeterministicInterfaceEquivalence`; it is imported directly.
   * The withdrawn `ObservableEventAtoms` theorem used a duplicate event-algebra
     owner and an unused `[Finite X]`; neither is reused here.
   * Pinned Mathlib's `Set.isAtom_iff` and `Set.isAtom_singleton` classify atoms
     of the full powerset, not minimal elements of the pullback subalgebra.
   * Current-tree and pinned-Mathlib searches found no exact characterization of
     minimal nonempty pullback events by realized readout fibers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.PullbackAlgebraFiberAtoms

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence

universe u

/-- Without any finiteness assumption, a nonempty event that is minimal among
nonempty events in the canonical pullback algebra is exactly one realized
readout fiber. -/
theorem nonzero_pullback_atoms_are_effective_fibers
    {X O : Type u} (q : Concept X O) :
    forall event : Set X,
      (event.Nonempty /\ event ∈ PullbackAlgebra q /\
          forall candidate : Set X,
            candidate.Nonempty ->
              candidate ∈ PullbackAlgebra q ->
                candidate ⊆ event -> event ⊆ candidate) <->
        exists observed : Set.range q,
          event = {state | q state = observed.1} := by
  intro event
  constructor
  · rintro ⟨⟨state, stateInEvent⟩, eventObservable, minimal⟩
    let fiber : Set X := {candidate | q candidate = q state}
    have fiberNonempty : fiber.Nonempty := ⟨state, rfl⟩
    have fiberObservable : fiber ∈ PullbackAlgebra q := by
      change Function.FactorsThrough fiber q
      intro first second sameReadout
      apply propext
      change (q first = q state) <-> q second = q state
      rw [sameReadout]
    have fiberSubset : fiber ⊆ event := by
      intro candidate sameFiber
      have sameTruthValue := eventObservable sameFiber
      exact Eq.mpr sameTruthValue stateInEvent
    have eventSubset := minimal fiber fiberNonempty fiberObservable fiberSubset
    refine ⟨⟨q state, Set.mem_range_self state⟩, ?_⟩
    ext candidate
    constructor
    · intro candidateInEvent
      exact eventSubset candidateInEvent
    · intro candidateInFiber
      exact fiberSubset candidateInFiber
  · rintro ⟨observed, rfl⟩
    obtain ⟨state, stateObserved⟩ := observed.property
    have fiberNonempty :
        Set.Nonempty {candidate : X | q candidate = observed.1} :=
      ⟨state, stateObserved⟩
    refine ⟨fiberNonempty, ?_, ?_⟩
    · change Function.FactorsThrough
        (fun candidate => q candidate = observed.1) q
      intro first second sameReadout
      apply propext
      change (q first = observed.1) <-> q second = observed.1
      rw [sameReadout]
    · intro candidate candidateNonempty candidateObservable candidateSubset
      obtain ⟨witness, witnessInCandidate⟩ := candidateNonempty
      have witnessObserved : q witness = observed.1 :=
        candidateSubset witnessInCandidate
      intro current currentObserved
      have sameTruthValue := candidateObservable
        (currentObserved.trans witnessObserved.symm)
      exact Eq.mpr sameTruthValue witnessInCandidate

#print axioms nonzero_pullback_atoms_are_effective_fibers

end D5.S3.ConceptDynamics.RefinementAlgebra.PullbackAlgebraFiberAtoms

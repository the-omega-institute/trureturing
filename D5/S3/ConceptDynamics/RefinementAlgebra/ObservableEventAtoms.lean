/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAtoms
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAtoms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonempty atoms of a finite observable-event algebra are its effective fibers. -/

import D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality
import Mathlib.Data.Fintype.Basic

/- Library-search audit trail (2026-08-25):
   * Exact current-tree hit `observableEventAlgebra` is the source's event
     algebra on `Set X`; it is imported and used directly.
   * Pinned Mathlib hits `Set.isAtom_iff` and `Set.isAtom_singleton` concern the
     full powerset lattice, not the fiber-constant observable subalgebra.
   * Repository and pinned-Mathlib searches found no theorem characterizing
     the nonempty minimal observable events as effective readout fibers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAtoms

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality

universe u

/-- For a finite state carrier, a nonempty observable event is minimal among
nonempty observable events exactly when it is the fiber of one realized
readout value. -/
theorem nonzero_observable_atoms_are_effective_fibers
    {X O : Type u} [Finite X] (q : Concept X O) :
    forall event : Set X,
      (event.Nonempty ∧ event ∈ observableEventAlgebra q ∧
          forall candidate : Set X,
            candidate.Nonempty ->
              candidate ∈ observableEventAlgebra q ->
                candidate ⊆ event -> event ⊆ candidate) <->
        exists observed : Set.range q,
          event = {state | q state = observed.1} := by
  intro event
  constructor
  · rintro ⟨⟨state, stateInEvent⟩, eventObservable, minimal⟩
    let fiber : Set X := {candidate | q candidate = q state}
    have fiberNonempty : fiber.Nonempty := ⟨state, rfl⟩
    have fiberObservable : fiber ∈ observableEventAlgebra q := by
      intro first second sameReadout
      change (q first = q state) <-> q second = q state
      rw [sameReadout]
    have fiberSubset : fiber ⊆ event := by
      intro candidate sameFiber
      exact (eventObservable sameFiber).mpr stateInEvent
    have eventSubset := minimal fiber fiberNonempty fiberObservable fiberSubset
    refine ⟨⟨q state, Set.mem_range_self state⟩, ?_⟩
    ext candidate
    constructor
    · intro candidateInEvent
      change candidate ∈ fiber
      exact eventSubset candidateInEvent
    · intro candidateInFiber
      apply fiberSubset
      change candidate ∈ fiber at candidateInFiber
      exact candidateInFiber
  · rintro ⟨observed, rfl⟩
    obtain ⟨state, stateObserved⟩ := observed.property
    have fiberNonempty :
        Set.Nonempty {candidate : X | q candidate = observed.1} := by
      exact ⟨state, stateObserved⟩
    refine ⟨fiberNonempty, ?_, ?_⟩
    · intro first second sameReadout
      change (q first = observed.1) <-> q second = observed.1
      rw [sameReadout]
    · intro candidate candidateNonempty candidateObservable candidateSubset
      obtain ⟨witness, witnessInCandidate⟩ := candidateNonempty
      have witnessObserved : q witness = observed.1 :=
        candidateSubset witnessInCandidate
      intro state stateObserved
      exact (candidateObservable (stateObserved.trans witnessObserved.symm)).mpr
        witnessInCandidate

#print axioms nonzero_observable_atoms_are_effective_fibers

end D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAtoms

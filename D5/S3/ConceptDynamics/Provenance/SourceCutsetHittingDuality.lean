/- GID: D5/S3/ConceptDynamics/Provenance/SourceCutsetHittingDuality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Provenance/SourceCutsetHittingDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Source cuts are exactly hitting sets of all minimal proof supports. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Order.Lattice.Nat

/- Library-search audit trail (2026-08-27):
   * Repository searches for source cuts, minimal proof supports, hitting
     cardinalities, and the defining body shapes found no exact declaration.
     The adjacent conflict-repair theorem concerns satisfiability cores rather
     than source availability and cannot supply either public clause here.
   * Pinned Mathlib supplies `Finset.card_lt_card`, `Nat.find_spec`,
     `Nat.find_min`, and the natural-number `sInf`; these generic primitives
     construct the minimal supporting subset and both cardinality minima.
   * No pinned-library theorem combines provenance cuts, minimal supports, and
     their minimum hitting cardinality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Provenance.SourceCutsetHittingDuality

/-- A support is minimal when it proves the conclusion and none of its proper
subsets does. -/
def IsMinimalProofSupport {Source : Type*}
    (provable : Finset Source -> Prop) (support : Finset Source) : Prop :=
  provable support ∧
    forall smaller : Finset Source, smaller ⊂ support -> ¬provable smaller

/-- Removing a source set is a cut when the remaining sources no longer prove
the conclusion. -/
def IsSourceCut {Source : Type*} [Fintype Source] [DecidableEq Source]
    (provable : Finset Source -> Prop) (removed : Finset Source) : Prop :=
  ¬provable (Finset.univ \ removed)

/-- A removal hits every minimal support when each such support loses at least
one source. -/
def HitsEveryMinimalProofSupport {Source : Type*} [DecidableEq Source]
    (provable : Finset Source -> Prop) (removed : Finset Source) : Prop :=
  forall support : Finset Source,
    IsMinimalProofSupport provable support -> (removed ∩ support).Nonempty

/-- Proof resilience is the least cardinality of a source cut. -/
noncomputable def proofResilience {Source : Type*}
    [Fintype Source] [DecidableEq Source]
    (provable : Finset Source -> Prop) : Nat :=
  sInf {size : Nat | ∃ removed : Finset Source,
    IsSourceCut provable removed ∧ removed.card = size}

/-- The minimum hitting cardinality is computed independently from the family
of minimal proof supports. -/
noncomputable def minimumHittingCardinality {Source : Type*} [DecidableEq Source]
    (provable : Finset Source -> Prop) : Nat :=
  sInf {size : Nat | ∃ removed : Finset Source,
    HitsEveryMinimalProofSupport provable removed ∧ removed.card = size}

/-- For a finite monotone provenance semantics, a removal destroys every proof
exactly when it hits every minimal proof support. Consequently the least cut
size equals the minimum hitting-set cardinality of the minimal-support family. -/
theorem source_cutset_hitting_duality
    {Source : Type*} [Fintype Source] [DecidableEq Source]
    (provable : Finset Source -> Prop) (provableMonotone : Monotone provable) :
    (forall removed : Finset Source,
      IsSourceCut provable removed ↔
        HitsEveryMinimalProofSupport provable removed) ∧
      proofResilience provable = minimumHittingCardinality provable := by
  classical
  have duality (removed : Finset Source) :
      IsSourceCut provable removed ↔
        HitsEveryMinimalProofSupport provable removed := by
    constructor
    · intro isCut support minimalSupport
      by_contra noHit
      apply isCut
      apply provableMonotone _ minimalSupport.1
      intro source sourceInSupport
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro sourceRemoved
      exact noHit ⟨source, Finset.mem_inter.mpr ⟨sourceRemoved, sourceInSupport⟩⟩
    · intro hitsEvery remainingProvable
      let candidateSize : Nat -> Prop := fun size =>
        ∃ support : Finset Source,
          support ⊆ Finset.univ \ removed ∧
            provable support ∧ support.card = size
      have candidateExists : ∃ size, candidateSize size :=
        ⟨(Finset.univ \ removed).card,
          Finset.univ \ removed, Finset.Subset.rfl, remainingProvable, rfl⟩
      rcases Nat.find_spec candidateExists with
        ⟨support, supportWithinRemaining, supportProvable, supportCard⟩
      have minimalSupport : IsMinimalProofSupport provable support := by
        refine ⟨supportProvable, ?_⟩
        intro smaller properSubset smallerProvable
        have smallerCandidate : candidateSize smaller.card :=
          ⟨smaller, properSubset.1.trans supportWithinRemaining,
            smallerProvable, rfl⟩
        have smallerCard : smaller.card < Nat.find candidateExists := by
          rw [← supportCard]
          exact Finset.card_lt_card properSubset
        exact Nat.find_min candidateExists smallerCard smallerCandidate
      rcases hitsEvery support minimalSupport with ⟨source, sourceHit⟩
      have sourceRemoved : source ∈ removed := (Finset.mem_inter.mp sourceHit).1
      have sourceInSupport : source ∈ support := (Finset.mem_inter.mp sourceHit).2
      have sourceRemaining := supportWithinRemaining sourceInSupport
      exact (Finset.mem_sdiff.mp sourceRemaining).2 sourceRemoved
  refine ⟨duality, ?_⟩
  apply congrArg sInf
  ext size
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨removed, isCut, cardEq⟩
    exact ⟨removed, (duality removed).mp isCut, cardEq⟩
  · rintro ⟨removed, hitsEvery, cardEq⟩
    exact ⟨removed, (duality removed).mpr hitsEvery, cardEq⟩

#print axioms source_cutset_hitting_duality

end D5.S3.ConceptDynamics.Provenance.SourceCutsetHittingDuality

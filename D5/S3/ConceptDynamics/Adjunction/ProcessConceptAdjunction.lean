/- GID: D5/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Adjunction/ProcessConceptAdjunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Process pullback is left adjoint to the maximal predictable future concept. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Logic.Relation
import Mathlib.Order.GaloisConnection.Defs

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'process_concept_adjunction' D5 Golden/Frozen/accepted` found no
     repository declaration or accepted duplicate.
   * Among the required all-D5 adjunction/Galois search results, the only actual
     adjunction declarations were the predicate adjunctions in
     `StrongestPostconditionAdjunction` and `RelationalPreconditionAdjunction`;
     neither concerns concept readouts.
   * Pinned Mathlib provides `Relation.EqvGen.setoid`, `Quotient.lift`, and
     `GaloisConnection`. The construction below reuses all three: the first two
     construct the required join explicitly, and the last packages the adjunction.
   * `ConceptJoinUniversal.Refines` was inspected directly. Its direction is that
     the left readout factors through the right readout, which fixes both sides of
     the equivalence below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Adjunction.ProcessConceptAdjunction

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

universe u

/-- A concept readout bundled with its coordinate type. -/
structure ReadoutConcept (X : Type u) where
  Coordinate : Type u
  readout : Concept X Coordinate

instance {X : Type u} : LE (ReadoutConcept X) where
  le C D := Refines C.readout D.readout

instance {X : Type u} : Preorder (ReadoutConcept X) where
  le_refl C := ⟨id, by funext x; rfl⟩
  le_trans A B C hAB hBC := by
    rcases hAB with ⟨factorAB, hAB⟩
    rcases hBC with ⟨factorBC, hBC⟩
    refine ⟨factorAB ∘ factorBC, ?_⟩
    rw [hAB, hBC]
    funext x
    rfl

/-- Pull a future concept readout back along a process. -/
def pullbackConcept {X Y : Type u} (process : X → Y) (D : ReadoutConcept Y) :
    ReadoutConcept X :=
  ⟨D.Coordinate, D.readout ∘ process⟩

/-- The generating identifications attach each current readout to its future image. -/
inductive FutureGlue {X Y : Type u} (process : X → Y) (C : ReadoutConcept X) :
    Y ⊕ C.Coordinate → Y ⊕ C.Coordinate → Prop
  | glue (x : X) : FutureGlue process C (Sum.inl (process x)) (Sum.inr (C.readout x))

/-- Coordinates of the maximal predictable future concept, constructed as a quotient. -/
abbrev FutureCoordinate {X Y : Type u} (process : X → Y) (C : ReadoutConcept X) :=
  Quotient (Relation.EqvGen.setoid (FutureGlue process C))

/-- The maximal future readout predictable from `C` along `process`.

This chooses option (甲): the required join is constructed, rather than assumed. The quotient
glues each `process x` to `C.readout x`; its equivalence closure supplies exactly the effective
identifications forced by current fibers, including points outside the process image. -/
def pushforwardConcept {X Y : Type u} (process : X → Y) (C : ReadoutConcept X) :
    ReadoutConcept Y :=
  ⟨FutureCoordinate process C,
    fun y ↦ Quotient.mk (Relation.EqvGen.setoid (FutureGlue process C)) (Sum.inl y)⟩

/-- Process pullback and the explicitly constructed maximal predictable future concept satisfy
the defining adjunction equivalence. -/
theorem process_concept_adjunction {X Y : Type u} (process : X → Y)
    (D : ReadoutConcept Y) (C : ReadoutConcept X) :
    pullbackConcept process D ≤ C ↔ D ≤ pushforwardConcept process C := by
  constructor
  · rintro ⟨predict, hpredict⟩
    let factor : FutureCoordinate process C → D.Coordinate :=
      Quotient.lift (Sum.elim D.readout predict) (by
        intro a b hab
        induction hab with
        | rel a b hab =>
            cases hab with
            | glue x => exact congrFun hpredict x
        | refl a => rfl
        | symm a b hab ih => exact ih.symm
        | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc)
    refine ⟨factor, ?_⟩
    funext y
    rfl
  · rintro ⟨factor, hfactor⟩
    refine ⟨fun c ↦ factor (Quotient.mk _ (Sum.inr c)), ?_⟩
    funext x
    have hglue :
        (Quotient.mk _ (Sum.inl (process x)) : FutureCoordinate process C) =
          Quotient.mk _ (Sum.inr (C.readout x)) :=
      Quotient.sound
        (Relation.EqvGen.rel _ _ (FutureGlue.glue x))
    change D.readout (process x) = factor (Quotient.mk _ (Sum.inr (C.readout x)))
    rw [hfactor]
    exact congrArg factor hglue

/-- The pointwise equivalence packages directly as Mathlib's `GaloisConnection`. -/
theorem process_concept_galois_connection {X Y : Type u} (process : X → Y) :
    GaloisConnection (pullbackConcept process) (pushforwardConcept process) :=
  process_concept_adjunction process

/-- Pullback is monotone for concept refinement, as supplied by the adjunction. -/
theorem pullback_concept_monotone {X Y : Type u} (process : X → Y) :
    Monotone (pullbackConcept process) :=
  (process_concept_galois_connection process).monotone_l

/-- The maximal predictable future construction is monotone, as supplied by the adjunction. -/
theorem pushforward_concept_monotone {X Y : Type u} (process : X → Y) :
    Monotone (pushforwardConcept process) :=
  (process_concept_galois_connection process).monotone_u

/-- Pulling the maximal predictable future back is refined by the current concept. -/
theorem pullback_pushforward_refines {X Y : Type u} (process : X → Y)
    (C : ReadoutConcept X) :
    pullbackConcept process (pushforwardConcept process C) ≤ C :=
  (process_concept_galois_connection process).l_u_le C

example :
    pullbackConcept (id : Bool → Bool) ⟨Bool, id⟩ ≤ ⟨Bool, id⟩ ↔
      (⟨Bool, id⟩ : ReadoutConcept Bool) ≤
        pushforwardConcept (id : Bool → Bool) ⟨Bool, id⟩ :=
  process_concept_adjunction (id : Bool → Bool) ⟨Bool, id⟩ ⟨Bool, id⟩

#print axioms process_concept_adjunction

end D5.S3.ConceptDynamics.Adjunction.ProcessConceptAdjunction

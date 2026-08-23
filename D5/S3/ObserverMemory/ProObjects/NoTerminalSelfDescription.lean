/- GID: D5/S3/ObserverMemory/ProObjects/NoTerminalSelfDescription
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ProObjects/NoTerminalSelfDescription
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A terminal pro-object stage cannot contain its twisted self-evaluation concept. -/

import D5.S0.Diagonal.Naturality.RelativeDiagonalEscape
import D5.S3.ObserverMemory.ProObjects.ConceptAnchorHomAsymmetry

/- Library-search audit trail (2026-08-23):
   * Exact repository hit `relative_diagonal_escape` proves that the twisted
     self-evaluation concept lies outside the stage listing's range. It is
     imported and applied directly below.
   * Canonical repository hits `presentedObject` and `constantObject` encode
     the source's terminal faithful-stage clause and are imported without forks.
   * Pinned Mathlib hit `Function.exists_fixed_point_of_surjective` is related,
     while `Function.cantor_surjective` is the set-valued specialization; the
     repository theorem is the exact explicit-witness match.
   * Exact atom-id search outside the digestion ledger and source documentation missed. -/

namespace D5.S3.ObserverMemory.ProObjects.NoTerminalSelfDescription

open CategoryTheory
open D5.S0.Diagonal.Naturality.RelativeDiagonalEscape
open D5.S3.ObserverMemory.ProObjects.ConceptAnchorHomAsymmetry

universe u

/-- Even when one stage explicitly presents the whole pro-object as a constant
object, a fixed-point-free twist sends the listing's self-evaluation concept
outside the range of that stage's same-typed concept listing. -/
theorem no_terminal_self_description
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (stages : Jᵒᵖ ⥤ Type u) (i : Jᵒᵖ) (Y : Type u)
    (_terminalRepresentation :
      presentedObject stages ≅ constantObject (stages.obj i))
    (enumeration : stages.obj i -> stages.obj i -> Y)
    (twist : Y -> Y) (fixedPointFree : forall y, twist y ≠ y) :
    (fun x => twist (enumeration x x)) ∉ Set.range enumeration := by
  exact relative_diagonal_escape enumeration twist fixedPointFree

#print axioms no_terminal_self_description

end D5.S3.ObserverMemory.ProObjects.NoTerminalSelfDescription

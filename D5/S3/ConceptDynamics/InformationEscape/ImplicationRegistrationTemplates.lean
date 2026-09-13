/- GID: D5/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ImplicationRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Indexed implication preserves both state-dependent predicate readouts with checked slot sensitivity. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import LeanInformationAudit.RegistrationWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrationTemplates

open LeanInformationAudit

/-- Two CUT slots retain the finite Boolean functions of the antecedent and consequent. -/
def implicationSignature (X Y : Type) [Fintype Y] : PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Y → Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

/-- Reflect each supplied predicate at the current state, without theorem-based reduction. -/
def implicationRealization {X Y : Type} [Fintype Y] (P Q : X → Y → Prop)
    [∀ x, DecidablePred (P x)] [∀ x, DecidablePred (Q x)] : PrimitiveRealization (implicationSignature X Y) where
  readout | false => fun x y => decide (P x y) | true => fun x y => decide (Q x y)
  anchor := Fin.elim0

/-- A fixed implication law; callers supply the arena, never an arbitrary Law. -/
def implicationArena (A : Arena) (Y : Type) [Fintype Y] : PrimitiveLawArena where
  toArena := A
  signature := implicationSignature A.State Y
  Law r := ∀ x y, r.readout false x y = true → r.readout true x y = true

/-- Boolean reflection preserves the complete pointwise implication. -/
theorem implicationLegacy (A : Arena) {Y : Type} [Fintype Y] (P Q : A.State → Y → Prop)
    [∀ x, DecidablePred (P x)] [∀ x, DecidablePred (Q x)] :
    LegacyPrimitiveRealization (implicationArena A Y) (∀ x y, P x y → Q x y)
      (implicationRealization P Q) := by
  refine ⟨?_⟩
  change (∀ x y, P x y → Q x y) ↔
    (∀ x y, decide (P x y) = true → decide (Q x y) = true)
  simp only [decide_eq_true_eq]

/-- Switching either readout alone changes the law when the arena and index are inhabited. -/
theorem implication_sensitivity (A : Arena) {Y : Type} [Fintype Y]
    (x : A.State) (y : Y) : FiniteSlotSensitivity (implicationArena A Y) := by
  constructor
  · intro i
    cases i with
    | false =>
        refine ⟨implicationRealization (fun _ _ => False) (fun _ _ => False),
          implicationRealization (fun _ _ => True) (fun _ _ => False), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · exact (hj rfl).elim
          · rfl
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => Bool.noConfusion (h x y rfl),
            fun _ _ _ h => Bool.noConfusion h⟩
    | true =>
        refine ⟨implicationRealization (fun _ _ => True) (fun _ _ => True),
          implicationRealization (fun _ _ => True) (fun _ _ => False), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · rfl
          · exact (hj rfl).elim
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => Bool.noConfusion (h x y rfl), fun _ _ _ _ => rfl⟩
  · intro i; exact Fin.elim0 i

#print axioms implicationLegacy
#print axioms implication_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.ImplicationRegistrationTemplates

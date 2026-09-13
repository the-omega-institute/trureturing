/- GID: D5/S3/ConceptDynamics/InformationEscape/CardinalityRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/CardinalityRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cardinality equality counts a Boolean ADMIT readout on the original finite states. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import LeanInformationAudit.RegistrationWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.CardinalityRegistrationTemplates

open LeanInformationAudit

/-- A single ADMIT slot retains which source states are counted. -/
def cardinalitySignature (X : Type) : PrimitiveSignature X where
  Index := Unit
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .admit
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def cardinalityRealization {X : Type} (admitted : X → Bool) :
    PrimitiveRealization (cardinalitySignature X) := ⟨fun _ => admitted, Fin.elim0⟩

/-- The target is fixed; varying the admission readout changes the counted states. -/
def cardinalityArena (A : Arena) (target : Nat) : PrimitiveLawArena where
  toArena := A
  signature := cardinalitySignature A.State
  Law r := by
    letI := A.stateFintype
    let admitted : A.State → Bool := r.readout ()
    exact (Finset.univ.filter (fun x => admitted x = true)).card = target

/-- All states are admitted. Only the constant-true filter is normalized in this bridge. -/
theorem cardinalityLegacy (X : Type) [Fintype X] [DecidableEq X] (target : Nat) :
    LegacyPrimitiveRealization (cardinalityArena (Arena.ofFintype X) target)
      (Fintype.card X = target) (cardinalityRealization (fun _ => true)) := by
  constructor
  simp [cardinalityArena, cardinalityRealization, Arena.ofFintype]

/-- Admitting all versus no states witnesses the sole slot whenever the target is nonzero. -/
theorem cardinality_sensitivity (X : Type) [Fintype X] [DecidableEq X] (target : Nat)
    (hcard : Fintype.card X = target) (hne : target ≠ 0) :
    FiniteSlotSensitivity (cardinalityArena (Arena.ofFintype X) target) := by
  constructor
  · intro i
    cases i
    refine ⟨cardinalityRealization (fun _ => true),
      cardinalityRealization (fun _ => false), ?_, ?_, ?_⟩
    · intro j hj; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
    · have hall := (cardinalityLegacy X target).equivalence.mp hcard
      have hnone : ¬ (cardinalityArena (Arena.ofFintype X) target).Law
          (cardinalityRealization (fun _ => false)) := by
        simpa [cardinalityArena, cardinalityRealization, Arena.ofFintype] using Ne.symm hne
      exact ⟨fun _ => hnone, fun _ => hall⟩
  · intro i; exact Fin.elim0 i

#print axioms cardinalityLegacy
#print axioms cardinality_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.CardinalityRegistrationTemplates

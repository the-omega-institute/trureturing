/- GID: D5/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ExistentialWitnessRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Existential witness registration uses one ADMIT slot over complete witness states with checked slot sensitivity. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import LeanInformationAudit.RegistrationWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates

open LeanInformationAudit

/-- A complete witness is a state; its acceptance is the single ADMIT readout. -/
def existentialWitnessSignature (X : Type) : PrimitiveSignature X where
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

def existentialWitnessRealization {X : Type} (P : X → Prop) [DecidablePred P] :
    PrimitiveRealization (existentialWitnessSignature X) :=
  ⟨fun _ x => decide (P x), Fin.elim0⟩

/-- The fixed law asks for an accepted state, with no raw Law parameter. -/
def existentialWitnessArena (A : Arena) : PrimitiveLawArena where
  toArena := A
  signature := existentialWitnessSignature A.State
  Law r := ∃ x, r.readout () x = true

theorem existentialWitnessLegacy (A : Arena) (P : A.State → Prop) [DecidablePred P] :
    LegacyPrimitiveRealization (existentialWitnessArena A) (∃ x, P x)
      (existentialWitnessRealization P) := by
  refine ⟨?_⟩
  change (∃ x, P x) ↔ ∃ x, decide (P x) = true
  simp only [admit_readout_eq_true_iff P]

/-- Accepting every state and rejecting every state toggle the only slot. -/
theorem existentialWitness_sensitivity (A : Arena) (x : A.State) :
    FiniteSlotSensitivity (existentialWitnessArena A) := by
  constructor
  · intro i
    refine ⟨existentialWitnessRealization (fun _ => True),
      existentialWitnessRealization (fun _ => False), ?_, ?_, ?_⟩
    · intro j hj
      cases i; cases j
      exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
    · exact ⟨fun _ ⟨_, h⟩ => Bool.false_ne_true h, fun _ => ⟨x, rfl⟩⟩
  · intro i; exact Fin.elim0 i

#print axioms existentialWitnessLegacy
#print axioms existentialWitness_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.ExistentialWitnessRegistrationTemplates

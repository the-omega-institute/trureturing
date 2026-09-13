/- GID: D5/S3/ConceptDynamics/InformationEscape/InclusionRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/InclusionRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two ADMIT slots express inclusion on finite supports with a complete support bridge and independent slot sensitivity. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import LeanInformationAudit.RegistrationWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.InclusionRegistrationTemplates

open LeanInformationAudit

/-- Inclusion retains both membership tests as independent ADMIT slots. -/
def inclusionSignature (X : Type) : PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .admit
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def inclusionRealization {X : Type} (P Q : X → Prop)
    [DecidablePred P] [DecidablePred Q] : PrimitiveRealization (inclusionSignature X) where
  readout | false => fun x => decide (P x) | true => fun x => decide (Q x)
  anchor := Fin.elim0

def inclusionArena (A : Arena) : PrimitiveLawArena where
  toArena := A
  signature := inclusionSignature A.State
  Law r := ∀ x, r.readout false x = true → r.readout true x = true

/-- The union contains every possible counterexample, even for an infinite ambient type.
No inclusion theorem or theorem-dependent reduction is used in this bridge. -/
theorem inclusionLegacy {X : Type} [DecidableEq X] (S T : Finset X) :
    LegacyPrimitiveRealization (inclusionArena (Arena.ofFintype ↥(S ∪ T))) (S ⊆ T)
      (inclusionRealization (fun x : ↥(S ∪ T) => x.val ∈ S) (fun x => x.val ∈ T)) := by
  constructor
  change (S ⊆ T) ↔ ∀ x : ↥(S ∪ T), decide (x.val ∈ S) = true → decide (x.val ∈ T) = true
  simp only [decide_eq_true_eq]
  constructor
  · intro h x hx
    exact h hx
  · intro h x hx
    exact h ⟨x, Finset.mem_union.mpr (Or.inl hx)⟩ hx

/-- Changing either membership slot alone can falsify the law. -/
theorem inclusion_sensitivity (A : Arena) (x : A.State) :
    FiniteSlotSensitivity (inclusionArena A) := by
  constructor
  · intro i
    cases i with
    | false =>
        refine ⟨inclusionRealization (fun _ => False) (fun _ => False),
          inclusionRealization (fun _ => True) (fun _ => False), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · exact (hj rfl).elim
          · rfl
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => Bool.noConfusion (h x rfl),
            fun _ _ h => Bool.noConfusion h⟩
    | true =>
        refine ⟨inclusionRealization (fun _ => True) (fun _ => True),
          inclusionRealization (fun _ => True) (fun _ => False), ?_, ?_, ?_⟩
        · intro j hj; cases j
          · rfl
          · exact (hj rfl).elim
        · intro j; exact Fin.elim0 j
        · exact ⟨fun _ h => Bool.noConfusion (h x rfl), fun _ _ _ => rfl⟩
  · intro i; exact Fin.elim0 i

#print axioms inclusionLegacy
#print axioms inclusion_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.InclusionRegistrationTemplates

/- GID: D5/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/MapInjectiveRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A single typed CUT readout retains map injectivity and supplies checked slot sensitivity. -/

import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S0.History.HistoryCarrier
import LeanInformationAudit.RegistrationWitnesses
import LeanInformationAudit.Syntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates

open RegistrationTemplates LeanInformationAudit

/-- The complete map is the only CUT slot; its values are not truth labels. -/
abbrev mapInjectiveSignature (X Y : Type) [DecidableEq Y] := cutSignature X Y

def mapInjectiveRealization {X Y : Type} [DecidableEq Y] (f : X → Y) :
    PrimitiveRealization (mapInjectiveSignature X Y) := cutRealization f

register_information_template mapInjectiveRealization constructors 1
  [D5.S0.History.Marker, D5.S0.History.Opcode]

def mapInjectiveArena (A : Arena) (Y : Type) [DecidableEq Y] : PrimitiveLawArena where
  toArena := A
  signature := mapInjectiveSignature A.State Y
  Law r := Function.Injective (r.readout ())

theorem mapInjectiveLegacy (A : Arena) {Y : Type} [DecidableEq Y] (f : A.State → Y) :
    LegacyPrimitiveRealization (mapInjectiveArena A Y) (Function.Injective f)
      (mapInjectiveRealization f) := ⟨Iff.rfl⟩

/-- Replacing an injective map by a constant changes the law on two distinct states. -/
theorem mapInjective_sensitivity (A : Arena) {Y : Type} [DecidableEq Y]
    (f : A.State → Y) (hf : Function.Injective f) (x y : A.State) (hne : x ≠ y) :
    FiniteSlotSensitivity (mapInjectiveArena A Y) := by
  constructor
  · intro i
    cases i
    refine ⟨mapInjectiveRealization f, mapInjectiveRealization (fun _ => f x), ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ h => hne (h rfl), fun _ => hf⟩
  · intro i
    exact Fin.elim0 i

#print axioms mapInjectiveLegacy
#print axioms mapInjective_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.MapInjectiveRegistrationTemplates

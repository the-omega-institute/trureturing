/- GID: D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Boolean predicate readouts retain pointwise iff statements and checked slot sensitivity. -/

import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates

open PointwiseRegistrationTemplates
open LeanInformationAudit

abbrev iffSignature (X : Type) := homogeneousPointwiseEqSignature X Bool

def iffRealization {X : Type} (left right : X → Bool) :
    PrimitiveRealization (iffSignature X) :=
  @homogeneousPointwiseEqRealization X Bool instDecidableEqBool left right

def iffArena (A : Arena) : PrimitiveLawArena := homogeneousPointwiseEqArena A Bool

theorem iffLegacy (A : Arena) (P Q : A.State → Prop)
    [dP : DecidablePred P] [dQ : DecidablePred Q] :
    LegacyPrimitiveRealization (iffArena A) (∀ x, P x ↔ Q x)
      (@iffRealization A.State (fun x => @decide (P x) (dP x)) (fun x => @decide (Q x) (dQ x))) := by
  classical
  refine ⟨?_⟩
  change (∀ x, P x ↔ Q x) ↔ (∀ x, decide (P x) = decide (Q x))
  simp

theorem iff_sensitivity (A : Arena) (x : A.State) :
    LeanInformationAudit.FiniteSlotSensitivity (iffArena A) := by
  exact homogeneousPointwiseEq_sensitivity (A := A) x false true (by decide)

#print axioms iffLegacy
#print axioms iff_sensitivity

end D5.S3.ConceptDynamics.InformationEscape.IffRegistrationTemplates

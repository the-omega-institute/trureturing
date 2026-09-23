/- GID: D5/S3/ConceptDynamics/InformationEscape/CertificateWordRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/CertificateWordRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Six-position certificate words retain each finite code in a separate CUT readout. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import LeanInformationAudit.Syntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates

open D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit

/-- Six indexed outputs retain the complete finite certificate word. -/
def certificateSignature (X : Type) : PrimitiveSignature X where
  Index := Fin 6
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Fin 5
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

/-- Read each of the six finite codes without changing its value. -/
def certificateWordRealization {X : Type} (readWord : X -> Fin 6 -> Fin 5) :
    PrimitiveRealization (certificateSignature X) where
  readout index state := readWord state index
  anchor := Fin.elim0

register_information_template certificateWordRealization

end D5.S3.ConceptDynamics.InformationEscape.CertificateWordRegistrationTemplates

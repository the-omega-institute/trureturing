/- GID: D5/S3/ConceptDynamics/InformationEscape/AgohCoefficientReadoutTemplate
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/AgohCoefficientReadoutTemplate
   mirror-E: none(waiver:content-template)
   anchors: []
   utility: none
   digest: Three indexed coefficient-code cuts for the alternating-numerator counterexample. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import LeanInformationAudit.Syntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit

namespace D5.S3.ConceptDynamics.InformationEscape.AgohCoefficientReadoutTemplate

def coefficientSignature (S : Type) : PrimitiveSignature S where
  Index := Fin 3
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Fin 9
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

def coefficientRealization {S : Type} (readCoefficients : S → Fin 3 → Fin 9) :
    PrimitiveRealization (coefficientSignature S) where
  readout index state := readCoefficients state index
  anchor := Fin.elim0

register_information_template coefficientRealization

end D5.S3.ConceptDynamics.InformationEscape.AgohCoefficientReadoutTemplate

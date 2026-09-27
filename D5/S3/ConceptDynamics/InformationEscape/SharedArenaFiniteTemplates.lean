/- GID: D5/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/SharedArenaFiniteTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous finite-output readouts retain two causal slots for shared-arena registrations. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates

open D5.S3.ConceptDynamics.InformationEscape

def finiteSignature (X : Type) : PrimitiveSignature X where
  Index := Bool
  indexFintype := inferInstance
  indexDecidableEq := instDecidableEqBool
  Output := fun _ => Fin 16
  outputDecidableEq := fun _ => instDecidableEqFin 16
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := instDecidableEqFin 0

def interventionFiniteRealization {X : Type} (f g : X → Fin 16) :
    PrimitiveRealization (finiteSignature X) where
  readout := fun b x => Bool.rec (f x) (g x) b
  anchor := Fin.elim0

def observationFiniteRealization {X : Type} (f g : X → Fin 16) :
    PrimitiveRealization (finiteSignature X) where
  readout := fun b x => Bool.rec (f x) (g x) b
  anchor := Fin.elim0

def finiteArena (A : Arena) : PrimitiveLawArena where
  toArena := A
  signature := finiteSignature A.State
  Law r := ∃ x y, r.readout false x = r.readout false y ∧
    r.readout true x ≠ r.readout true y

end D5.S3.ConceptDynamics.InformationEscape.SharedArenaFiniteTemplates

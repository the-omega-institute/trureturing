/- GID: D5/S3/ConceptDynamics/InformationEscape/GraphCutRegistrationTemplates
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/GraphCutRegistrationTemplates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A graph-gradient observation family with arbitrary vertices and finite edge set. -/

import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

namespace D5.S3.ConceptDynamics.InformationEscape.GraphCutRegistrationTemplates

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

universe u

/-- A finite role observes the full edge gradient of a binary vertex labeling.
The graph and vertex type remain arbitrary parameters. -/
def graphGradientSignature : Signature where
  Params := Σ V : Type u, SimpleGraph V
  State := fun p => p.1 → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => p.2.edgeSet → ZMod 2
  Anchor := Empty
  finiteAnchor := inferInstance

end D5.S3.ConceptDynamics.InformationEscape.GraphCutRegistrationTemplates

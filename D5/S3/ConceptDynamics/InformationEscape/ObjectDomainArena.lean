/- GID: D5/S3/ConceptDynamics/InformationEscape/ObjectDomainArena
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/ObjectDomainArena
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite readout arena can identify an independently typed, possibly infinite source domain. -/

import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

universe u v w z

/-- The source objects of a theorem need not be the finite states used to audit
its readouts. The law and its realization retain the ordinary finite arena;
`Domain` identifies the objects whose information the theorem concerns. -/
structure ObjectDomainArena extends PrimitiveLawArena.{u, v, w} where
  Domain : Type z

end D5.S3.ConceptDynamics.InformationEscape

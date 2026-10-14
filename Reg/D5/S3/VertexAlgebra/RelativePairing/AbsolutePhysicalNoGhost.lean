import D5.S3.VertexAlgebra.RelativePairing.AbsolutePhysicalNoGhost
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.RelativePairing.AbsolutePhysicalNoGhost

open _root_.D5.S3.VertexAlgebra.RelativePairing.AbsolutePhysicalNoGhost

abbrev RepresentativeTarget := type_of% (@original_absolute_ghost_one_representative)
abbrev LiteralImageTarget := type_of% (@absolute_degree_one_image)
abbrev BoundaryIntersectionTarget := type_of% (@ghostBoundary_unrestricted_intersection)
abbrev NoGhostTarget := type_of% (@absoluteCanonicalForm_noGhost)
abbrev RadicalsTarget := type_of% (@absoluteCanonicalForm_radicals_bot)
abbrev RecoveryTarget := type_of% (@absoluteCanonicalForm_recovery)
abbrev VanishingTarget := type_of% (@original_other_ghost_cohomology_zero)

theorem representative_sourceBridge :
    (type_of% (@original_absolute_ghost_one_representative)) ↔ RepresentativeTarget := Iff.rfl

theorem literalImage_sourceBridge :
    (type_of% (@absolute_degree_one_image)) ↔ LiteralImageTarget := Iff.rfl

theorem boundaryIntersection_sourceBridge :
    (type_of% (@ghostBoundary_unrestricted_intersection)) ↔ BoundaryIntersectionTarget := Iff.rfl

theorem noGhost_sourceBridge : (type_of% (@absoluteCanonicalForm_noGhost)) ↔ NoGhostTarget :=
  Iff.rfl

end Reg.D5.S3.VertexAlgebra.RelativePairing.AbsolutePhysicalNoGhost

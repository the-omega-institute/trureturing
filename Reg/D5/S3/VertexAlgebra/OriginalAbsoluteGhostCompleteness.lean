import D5.S3.VertexAlgebra.OriginalAbsoluteGhostCompleteness
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.OriginalAbsoluteGhostCompleteness

open _root_.D5.S3.VertexAlgebra.OriginalAbsoluteGhostCompleteness

abbrev RepresentativeTarget := type_of% (@absolute_ghost_one_representative)
abbrev VanishingTarget := type_of% (@other_ghost_cycle_boundary)
abbrev ProjectionDegreeTarget := type_of% (@energyProjection_ghost)

theorem representative_sourceBridge :
    (type_of% (@absolute_ghost_one_representative)) ↔ RepresentativeTarget := Iff.rfl

theorem vanishing_sourceBridge : (type_of% (@other_ghost_cycle_boundary)) ↔ VanishingTarget :=
  Iff.rfl

end Reg.D5.S3.VertexAlgebra.OriginalAbsoluteGhostCompleteness

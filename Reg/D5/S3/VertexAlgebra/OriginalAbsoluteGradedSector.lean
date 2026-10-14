import D5.S3.VertexAlgebra.OriginalAbsoluteGradedSector
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.OriginalAbsoluteGradedSector

open _root_.D5.S3.VertexAlgebra.OriginalAbsoluteGradedSector

abbrev FirstProjectorTarget := type_of% (@ungraded_ghost_one_projector)
abbrev SecondProjectorTarget := type_of% (@ungraded_ghost_two_projector)
abbrev OriginalBoundaryTarget := type_of% (@full_unrestricted_boundary_intersection)

theorem firstProjector_sourceBridge :
    (type_of% (@ungraded_ghost_one_projector)) ↔ FirstProjectorTarget := Iff.rfl

theorem originalBoundary_sourceBridge :
    (type_of% (@full_unrestricted_boundary_intersection)) ↔ OriginalBoundaryTarget := Iff.rfl

end Reg.D5.S3.VertexAlgebra.OriginalAbsoluteGradedSector

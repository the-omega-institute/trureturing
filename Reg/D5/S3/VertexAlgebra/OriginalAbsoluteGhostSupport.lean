import D5.S3.VertexAlgebra.OriginalAbsoluteGhostSupport
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.OriginalAbsoluteGhostSupport

open _root_.D5.S3.VertexAlgebra.OriginalAbsoluteGhostSupport

abbrev CoefficientTarget := type_of% (@native_ghost_support)
abbrev BranchTarget := type_of% (@projector_ghost_support)
abbrev RelativeTarget := type_of% (@ghost_one_projector_relative)
abbrev VanishingTarget := type_of% (@projector_other_ghost_vanishes)

theorem relative_sourceBridge : (type_of% (@ghost_one_projector_relative)) ↔ RelativeTarget :=
  Iff.rfl

theorem vanishing_sourceBridge : (type_of% (@projector_other_ghost_vanishes)) ↔ VanishingTarget :=
  Iff.rfl

end Reg.D5.S3.VertexAlgebra.OriginalAbsoluteGhostSupport

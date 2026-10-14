import D5.S3.VertexAlgebra.OriginalAbsoluteGhostDoublet
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.OriginalAbsoluteGhostDoublet

open _root_.D5.S3.VertexAlgebra.OriginalAbsoluteGhostDoublet

abbrev NativeRecoveryTarget := type_of% (@upState_coordinates)
abbrev QuotientLeftTarget := type_of% (@upQuotient_left_inverse)
abbrev QuotientRightTarget := type_of% (@upQuotient_right_inverse)

theorem nativeRecovery_sourceBridge : (type_of% (@upState_coordinates)) ↔ NativeRecoveryTarget :=
  Iff.rfl

theorem quotientRight_sourceBridge :
    (type_of% (@upQuotient_right_inverse)) ↔ QuotientRightTarget := Iff.rfl

end Reg.D5.S3.VertexAlgebra.OriginalAbsoluteGhostDoublet

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality

open _root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality
open LeanInformationAudit

noncomputable section

def wordEscapeFrom := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalRescaling.physicalWord
def wordContinuation : Contract.Continuation Unit := .unknown
abbrev wordContractObligation := Contract.Registration (@physicalWord_locality)
  (type_of% wordEscapeFrom) (type_of% wordEscapeFrom) Unit

end
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality

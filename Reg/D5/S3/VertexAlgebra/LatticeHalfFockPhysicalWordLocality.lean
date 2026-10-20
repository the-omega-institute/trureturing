import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality

/- Exact typed mirror is a faithful audit attempt, not a declared_validated
   four-slot registration. -/
abbrev sourceScope_physicalWord_locality :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality.physicalWord_locality)
theorem source_actual_physicalWord_locality : sourceScope_physicalWord_locality :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality.physicalWord_locality

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality

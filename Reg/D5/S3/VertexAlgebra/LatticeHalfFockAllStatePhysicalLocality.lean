import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality

/- Exact typed mirror is a faithful audit attempt, not a declared_validated
   four-slot registration. -/
abbrev sourceScope_correctedField_physical_locality :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality.correctedField_physical_locality)
theorem source_actual_correctedField_physical_locality : sourceScope_correctedField_physical_locality :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality.correctedField_physical_locality

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality

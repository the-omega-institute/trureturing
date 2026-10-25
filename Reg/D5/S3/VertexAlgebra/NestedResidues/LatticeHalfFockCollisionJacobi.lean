import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockCollisionJacobi

set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockCollisionJacobi
open _root_.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockCollisionJacobi

abbrev sourceScope := type_of% (@actual_nested_iterate)
theorem source_actual : sourceScope := @actual_nested_iterate

/- Exact original telescope includes K with actual A/B locality, three
independent whole-field locality families, all signed indices and both exact
finite ranges. A faithful Contract.Registration requires an enrolled dependent
field readout and whole-family variation, sensitivity, observational dependence
and structural sourceSelection. Those obligations remain unproved; this exact
source reconstruction does not assert declared_validated. -/
end Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockCollisionJacobi

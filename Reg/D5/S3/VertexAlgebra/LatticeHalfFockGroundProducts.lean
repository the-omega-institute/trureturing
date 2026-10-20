import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts

set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts
open _root_.D5.S3.ConceptDynamics.InformationEscape

/- Faithful source-scope attempts retain each original public theorem telescope. -/
abbrev sourceScope_ground_action_product := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts.ground_action_product)
theorem source_actual_ground_action_product : sourceScope_ground_action_product := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts.ground_action_product

abbrev sourceScope_ground_action_exchange := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts.ground_action_exchange)
theorem source_actual_ground_action_exchange : sourceScope_ground_action_exchange := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts.ground_action_exchange

/- Four-slot realization, source selection and whole-family sensitivity remain open; these declarations preserve the exact source types for the audit lane. -/
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts

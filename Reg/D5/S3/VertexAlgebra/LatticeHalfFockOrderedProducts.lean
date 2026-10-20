import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts

set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
open _root_.D5.S3.ConceptDynamics.InformationEscape

/- Exact source-type mirrors retain each original public theorem telescope; they are not registrations. -/
abbrev sourceScope_native_ordered_product := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.native_ordered_product)
theorem source_actual_native_ordered_product : sourceScope_native_ordered_product := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.native_ordered_product

/- Four-slot realization, source selection and whole-family sensitivity remain open; these declarations preserve the exact source types for the audit lane. -/
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts

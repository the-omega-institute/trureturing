import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts

set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
open _root_.D5.S3.ConceptDynamics.InformationEscape

/- Faithful source-scope attempts retain each original public theorem telescope. -/
abbrev sourceScope_native_ordered_product := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.native_ordered_product)
theorem source_actual_native_ordered_product : sourceScope_native_ordered_product := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.native_ordered_product

abbrev sourceScope_native_reverse_ordered_product := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.native_reverse_ordered_product)
theorem source_actual_native_reverse_ordered_product : sourceScope_native_reverse_ordered_product := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.native_reverse_ordered_product

abbrev sourceScope_tensor_kernel_bounds := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.tensor_kernel_bounds)
theorem source_actual_tensor_kernel_bounds : sourceScope_tensor_kernel_bounds := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.tensor_kernel_bounds

abbrev sourceScope_tensor_expansion_pure := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.tensor_expansion_pure)
theorem source_actual_tensor_expansion_pure : sourceScope_tensor_expansion_pure := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.tensor_expansion_pure

abbrev sourceScope_charged_tensor_ordered_product := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.charged_tensor_ordered_product)
theorem source_actual_charged_tensor_ordered_product : sourceScope_charged_tensor_ordered_product := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.charged_tensor_ordered_product

abbrev sourceScope_charged_tensor_reverse_ordered_product := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.charged_tensor_reverse_ordered_product)
theorem source_actual_charged_tensor_reverse_ordered_product : sourceScope_charged_tensor_reverse_ordered_product := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts.charged_tensor_reverse_ordered_product

/- Four-slot realization, source selection and whole-family sensitivity remain open; these declarations preserve the exact source types for the audit lane. -/
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockProductKernel

set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape

/- Exact source-type mirrors retain each original public theorem telescope; they are not registrations. -/
abbrev sourceScope_pair_translation_composition := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.pair_translation_composition)
theorem source_actual_pair_translation_composition : sourceScope_pair_translation_composition := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.pair_translation_composition

abbrev sourceScope_kernel_constant := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.kernel_constant)
theorem source_actual_kernel_constant : sourceScope_kernel_constant := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.kernel_constant

abbrev sourceScope_kernel_creator := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.kernel_creator)
theorem source_actual_kernel_creator : sourceScope_kernel_creator := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.kernel_creator

abbrev sourceScope_common_kernel_rectangular_support := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.common_kernel_rectangular_support)
theorem source_actual_common_kernel_rectangular_support : sourceScope_common_kernel_rectangular_support := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.common_kernel_rectangular_support

abbrev sourceScope_common_kernel_ordered_finite_support := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.common_kernel_ordered_finite_support)
theorem source_actual_common_kernel_ordered_finite_support : sourceScope_common_kernel_ordered_finite_support := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.common_kernel_ordered_finite_support

abbrev sourceScope_common_kernel_branch_exchange := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.common_kernel_branch_exchange)
theorem source_actual_common_kernel_branch_exchange : sourceScope_common_kernel_branch_exchange := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel.common_kernel_branch_exchange

/- Four-slot realization, source selection and whole-family sensitivity remain open; these declarations preserve the exact source types for the audit lane. -/
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockProductKernel

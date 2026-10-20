import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel

set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape

/- Exact source-type mirrors retain each original public theorem telescope; they are not registrations. -/
abbrev sourceScope_physical_difference_expansion := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel.physical_difference_expansion)
theorem source_actual_physical_difference_expansion : sourceScope_physical_difference_expansion := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel.physical_difference_expansion

abbrev sourceScope_physical_difference_iterate := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel.physical_difference_iterate)
theorem source_actual_physical_difference_iterate : sourceScope_physical_difference_iterate := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel.physical_difference_iterate

abbrev sourceScope_native_cleared_kernel_expansion := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel.native_cleared_kernel_expansion)
theorem source_actual_native_cleared_kernel_expansion : sourceScope_native_cleared_kernel_expansion := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel.native_cleared_kernel_expansion

abbrev sourceScope_cleared_polynomial_expansion := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel.cleared_polynomial_expansion)
theorem source_actual_cleared_polynomial_expansion : sourceScope_cleared_polynomial_expansion := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel.cleared_polynomial_expansion

abbrev sourceScope_native_cleared_kernel_exchange := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel.native_cleared_kernel_exchange)
theorem source_actual_native_cleared_kernel_exchange : sourceScope_native_cleared_kernel_exchange := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel.native_cleared_kernel_exchange

/- Four-slot realization, source selection and whole-family sensitivity remain open; these declarations preserve the exact source types for the audit lane. -/
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockClearedKernel

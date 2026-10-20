import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing

set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing
open _root_.D5.S3.ConceptDynamics.InformationEscape

/- Exact source-type mirrors retain each original public theorem telescope; they are not registrations. -/
abbrev sourceScope_half_contraction_two_branch_clearing := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.half_contraction_two_branch_clearing)
theorem source_actual_half_contraction_two_branch_clearing : sourceScope_half_contraction_two_branch_clearing := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.half_contraction_two_branch_clearing

abbrev sourceScope_half_contraction_physical_clearing := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.half_contraction_physical_clearing)
theorem source_actual_half_contraction_physical_clearing : sourceScope_half_contraction_physical_clearing := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.half_contraction_physical_clearing

abbrev sourceScope_cleared_polynomial_degree := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.cleared_polynomial_degree)
theorem source_actual_cleared_polynomial_degree : sourceScope_cleared_polynomial_degree := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.cleared_polynomial_degree

abbrev sourceScope_cleared_polynomial_reciprocity := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.cleared_polynomial_reciprocity)
theorem source_actual_cleared_polynomial_reciprocity : sourceScope_cleared_polynomial_reciprocity := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.cleared_polynomial_reciprocity

abbrev sourceScope_cleared_polynomial_coefficient_reciprocity := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.cleared_polynomial_coefficient_reciprocity)
theorem source_actual_cleared_polynomial_coefficient_reciprocity : sourceScope_cleared_polynomial_coefficient_reciprocity := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.cleared_polynomial_coefficient_reciprocity

abbrev sourceScope_physical_clearing_sign := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.physical_clearing_sign)
theorem source_actual_physical_clearing_sign : sourceScope_physical_clearing_sign := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing.physical_clearing_sign

/- Four-slot realization, source selection and whole-family sensitivity remain open; these declarations preserve the exact source types for the audit lane. -/
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing

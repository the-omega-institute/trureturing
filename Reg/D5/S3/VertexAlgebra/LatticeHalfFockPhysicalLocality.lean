import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality

set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality
open _root_.D5.S3.ConceptDynamics.InformationEscape

/- Faithful source-scope attempts retain each original public theorem telescope. -/
abbrev sourceScope_iterate_products_pure := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality.iterate_products_pure)
theorem source_actual_iterate_products_pure : sourceScope_iterate_products_pure := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality.iterate_products_pure

abbrev sourceScope_charged_coefficient_physical_locality := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality.charged_coefficient_physical_locality)
theorem source_actual_charged_coefficient_physical_locality : sourceScope_charged_coefficient_physical_locality := @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality.charged_coefficient_physical_locality

/- Four-slot realization, source selection and whole-family sensitivity remain open; these declarations preserve the exact source types for the audit lane. -/
end Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalLocality

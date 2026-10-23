import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceCompatibility

/-! Exact source telescopes for the matching-sector first-source law and its
    consumed additive closure.  No declared_validated registration is claimed;
    lawful source selection and the remaining issue #20510 audit obligations
    are still open. -/
set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceCompatibility
open _root_.D5.S3.VertexAlgebra
open LatticeHalfFockGroundRightCurrentTransport

abbrev sourceScope_compatible_add_left :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.compatible_add_left)

theorem source_actual_compatible_add_left : sourceScope_compatible_add_left :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.compatible_add_left

abbrev sourceScope_sectorProject_first_source_compatibility :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.sectorProject_first_source_compatibility)

theorem source_actual_sectorProject_first_source_compatibility :
    sourceScope_sectorProject_first_source_compatibility :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.sectorProject_first_source_compatibility

end Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceCompatibility

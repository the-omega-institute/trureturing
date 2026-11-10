import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetCompression

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetCompression

/- The exact source telescope and proof terms are available below. A lawful
source realization still requires the original polynomial/field readouts,
their exact reconstruction bridge and whole-family variation, sensitivity
and observational dependence. These declarations are source evidence only;
none is a Contract.Registration or a declared_validated four-slot audit. -/

abbrev sourceScope_projection_weightedPartial :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCompression.projection_weightedPartial)
theorem source_actual_projection_weightedPartial : sourceScope_projection_weightedPartial :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCompression.projection_weightedPartial

abbrev sourceScope_projection_current_polynomial :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCompression.projection_current_polynomial)
theorem source_actual_projection_current_polynomial : sourceScope_projection_current_polynomial :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCompression.projection_current_polynomial

abbrev sourceScope_projection_injection :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCompression.projection_injection)
theorem source_actual_projection_injection : sourceScope_projection_injection :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCompression.projection_injection

abbrev sourceScope_compressed_high_modes :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCompression.compressed_high_modes)
theorem source_actual_compressed_high_modes : sourceScope_compressed_high_modes :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCompression.compressed_high_modes

abbrev sourceScope_correction_finite :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCompression.correction_finite)
theorem source_actual_correction_finite : sourceScope_correction_finite :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCompression.correction_finite

end Reg.D5.S3.VertexAlgebra.LatticeCosetCompression

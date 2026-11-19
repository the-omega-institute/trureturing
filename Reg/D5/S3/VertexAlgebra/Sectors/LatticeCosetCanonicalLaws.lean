import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalLaws

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetCanonicalLaws

/- Exact original telescopes and proof terms are source evidence only.
   Source reconstruction, lawful enrolled readout, whole-family variation,
   per-role sensitivity and actual observational dependence remain required.
   These mirrors are not Contract.Registration or declared_validated. -/

abbrev sourceScope_projection_translation := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.projection_translation)
theorem source_actual_projection_translation : sourceScope_projection_translation :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.projection_translation

abbrev sourceScope_translation_injection := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.translation_injection)
theorem source_actual_translation_injection : sourceScope_translation_injection :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.translation_injection

abbrev sourceScope_source_derivative := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.source_derivative)
theorem source_actual_source_derivative : sourceScope_source_derivative :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.source_derivative

abbrev sourceScope_target_derivative := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.target_derivative)
theorem source_actual_target_derivative : sourceScope_target_derivative :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.target_derivative

end Reg.D5.S3.VertexAlgebra.LatticeCosetCanonicalLaws

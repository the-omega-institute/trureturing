import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetTransverse

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetTransverse

/- Source-bound proof terms do not supply the missing DependentFamily arena,
source reconstruction, lawful enrolled readout or the variation/sensitivity
and actual observational-dependence witnesses. No complete four-slot
registration is asserted by this source-only mirror. -/

abbrev sourceScope_transverse_translation :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetTransverse.transverse_translation)
theorem source_actual_transverse_translation : sourceScope_transverse_translation :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetTransverse.transverse_translation

abbrev sourceScope_transverse_polynomial_translation :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetTransverse.transverse_polynomial_translation)
theorem source_actual_transverse_polynomial_translation : sourceScope_transverse_polynomial_translation :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetTransverse.transverse_polynomial_translation

abbrev sourceScope_creationSeries_difference :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetTransverse.creationSeries_difference)
theorem source_actual_creationSeries_difference : sourceScope_creationSeries_difference :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetTransverse.creationSeries_difference

abbrev sourceScope_creationExponential_factorization :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetTransverse.creationExponential_factorization)
theorem source_actual_creationExponential_factorization :
    sourceScope_creationExponential_factorization :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetTransverse.creationExponential_factorization

end Reg.D5.S3.VertexAlgebra.LatticeCosetTransverse

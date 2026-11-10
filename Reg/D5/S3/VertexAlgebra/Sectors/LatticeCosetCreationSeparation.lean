import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetCreationSeparation

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetCreationSeparation

/- The exact source telescope alone supplies neither a lawful enrolled
readout nor sourceSelection, whole-family variation, sensitivity and actual
observational dependence. No declared_validated registration is asserted. -/

abbrev sourceScope_creationExponential_separation :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCreationSeparation.creationExponential_separation)
theorem source_actual_creationExponential_separation : sourceScope_creationExponential_separation :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCreationSeparation.creationExponential_separation

abbrev sourceScope_transverse_creation_coefficient :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCreationSeparation.transverse_creation_coefficient)
theorem source_actual_transverse_creation_coefficient : sourceScope_transverse_creation_coefficient :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCreationSeparation.transverse_creation_coefficient

end Reg.D5.S3.VertexAlgebra.LatticeCosetCreationSeparation

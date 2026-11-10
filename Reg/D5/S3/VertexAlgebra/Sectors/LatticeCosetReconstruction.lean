import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetReconstruction

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetReconstruction

open private native_normal_separation from D5.S3.VertexAlgebra.Sectors.LatticeCosetReconstruction

/- Exact source scopes alone do not supply enrolled readout or sourceSelection,
whole-family variation, sensitivity and actual observational dependence.
No declared_validated registration is asserted. -/

abbrev sourceScope_native_normal_separation := type_of% (@native_normal_separation)
theorem source_actual_native_normal_separation : sourceScope_native_normal_separation := @native_normal_separation

end Reg.D5.S3.VertexAlgebra.LatticeCosetReconstruction

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetGroundReconstruction

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetGroundReconstruction

/- Exact source scopes alone do not supply enrolled readout or sourceSelection,
whole-family variation, sensitivity and actual observational dependence.
No declared_validated registration is asserted. -/

abbrev sourceScope_ground_reconstruction := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetGroundReconstruction.ground_reconstruction)
theorem source_actual_ground_reconstruction : sourceScope_ground_reconstruction := @_root_.D5.S3.VertexAlgebra.LatticeCosetGroundReconstruction.ground_reconstruction

end Reg.D5.S3.VertexAlgebra.LatticeCosetGroundReconstruction

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetProjectedAction

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetProjectedAction

/- This exact telescope does not supply a complete Contract.Registration:
the lawful enrolled readout, source reconstruction and sourceSelection,
whole-family variation, sensitivity and observational dependence remain
required. No declared_validated status is asserted. -/

abbrev sourceScope_projected_transverse_polynomial :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetProjectedAction.projected_transverse_polynomial)
theorem source_actual_projected_transverse_polynomial : sourceScope_projected_transverse_polynomial :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetProjectedAction.projected_transverse_polynomial

end Reg.D5.S3.VertexAlgebra.LatticeCosetProjectedAction

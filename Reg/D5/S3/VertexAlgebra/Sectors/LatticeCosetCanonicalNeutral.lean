import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalNeutral

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetCanonicalNeutral

/- Exact original telescopes and proof terms are source evidence only.
   Source reconstruction, lawful enrolled readout, whole-family variation,
   per-role sensitivity and actual observational dependence remain required.
   These mirrors are not Contract.Registration or declared_validated. -/

abbrev sourceScope_neutral_action_invariance := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.neutral_action_invariance)
theorem source_actual_neutral_action_invariance : sourceScope_neutral_action_invariance :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.neutral_action_invariance

abbrev sourceScope_compressed_neutral := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.compressed_neutral)
theorem source_actual_compressed_neutral : sourceScope_compressed_neutral :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.compressed_neutral

end Reg.D5.S3.VertexAlgebra.LatticeCosetCanonicalNeutral

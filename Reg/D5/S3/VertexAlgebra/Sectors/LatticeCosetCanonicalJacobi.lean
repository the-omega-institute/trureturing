import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetCanonicalJacobi

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetCanonicalJacobi

/- Exact original telescopes and proof terms are source evidence only.
   Source reconstruction, lawful enrolled readout, whole-family variation,
   per-role sensitivity and actual observational dependence remain required.
   These mirrors are not Contract.Registration or declared_validated. -/

abbrev sourceScope_mixed_jacobi := type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.mixed_jacobi)
theorem source_actual_mixed_jacobi : sourceScope_mixed_jacobi :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetCanonicalIntertwiner.mixed_jacobi

end Reg.D5.S3.VertexAlgebra.LatticeCosetCanonicalJacobi

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeCosetInnerExpansion

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeCosetInnerExpansion

/- A faithful source telescope does not supply a lawful enrolled readout,
sourceSelection or whole-family variation, sensitivity and observational
dependence. No declared_validated registration is asserted. -/
abbrev sourceScope_compressed_multiplication_recursion :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeCosetInnerExpansion.compressed_multiplication_recursion)
theorem source_actual_compressed_multiplication_recursion :
    sourceScope_compressed_multiplication_recursion :=
  @_root_.D5.S3.VertexAlgebra.LatticeCosetInnerExpansion.compressed_multiplication_recursion

end Reg.D5.S3.VertexAlgebra.LatticeCosetInnerExpansion

import D5.S3.VertexAlgebra.LatticeHalfFockCurrentWard

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentWard

/-- Exact native source type retained for the four-slot registration attempt. -/
abbrev sourceScope_correctedField_current_ward :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.correctedField_current_ward)

theorem source_actual_correctedField_current_ward : sourceScope_correctedField_current_ward :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField.correctedField_current_ward

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockCurrentWard

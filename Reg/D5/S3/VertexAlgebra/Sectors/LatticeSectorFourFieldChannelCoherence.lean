import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Sectors.LatticeSectorFourFieldChannelCoherence

/-! This mirror preserves the complete source theorem telescope for the finite
four-field channel readout.  It is source-bound evidence only; the theorem
does not assert a separate validated registration. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorFourFieldChannelCoherence

abbrev sourceScope_actual_four_field_channel_readout_transport :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeSectorFourFieldChannelCoherence.actual_four_field_channel_readout_transport)

theorem source_actual_four_field_channel_readout_transport :
    sourceScope_actual_four_field_channel_readout_transport :=
  @_root_.D5.S3.VertexAlgebra.LatticeSectorFourFieldChannelCoherence.actual_four_field_channel_readout_transport

#print axioms source_actual_four_field_channel_readout_transport

end Reg.D5.S3.VertexAlgebra.Sectors.LatticeSectorFourFieldChannelCoherence

import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockNestedQForwardEdge
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockNestedQForwardEdge

/- The exact source bridge is compiled below. The four-slot escape audit is
   unfinished at the current source-boundary pin; issue #20163 records the
   missing sourceSelection/escapeFrom evidence. No declared_validated
   Contract.Registration is asserted for this theorem. -/
abbrev sourceScope_forward_weighted_identity_of_cutoff_le_lift :=
  type_of% (@_root_.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockNestedQForwardEdge.forward_weighted_identity_of_cutoff_le_lift)

theorem source_actual_forward_weighted_identity_of_cutoff_le_lift :
    sourceScope_forward_weighted_identity_of_cutoff_le_lift :=
  @_root_.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockNestedQForwardEdge.forward_weighted_identity_of_cutoff_le_lift

end Reg.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockNestedQForwardEdge

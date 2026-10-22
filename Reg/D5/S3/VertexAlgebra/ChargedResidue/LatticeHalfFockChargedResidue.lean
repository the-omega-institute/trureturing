import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.ChargedResidue.LatticeHalfFockChargedResidue

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue

open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue

/- These exact source mirrors preserve the original telescopes for the audit
   lane.  Four-slot family registrations are intentionally left open until the
   native two-order forward telescope and its complete-residue tail exist. -/
abbrev sourceScope_charged_ground_source_collision :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.charged_ground_source_collision)
theorem source_actual_charged_ground_source_collision : sourceScope_charged_ground_source_collision :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.charged_ground_source_collision

abbrev sourceScope_charged_source_pair_collision :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.charged_source_pair_collision)
theorem source_actual_charged_source_pair_collision : sourceScope_charged_source_pair_collision :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.charged_source_pair_collision

abbrev sourceScope_charged_ground_source_expansion :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.charged_ground_source_expansion)
theorem source_actual_charged_ground_source_expansion : sourceScope_charged_ground_source_expansion :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.charged_ground_source_expansion

abbrev sourceScope_projectedGround_slice_mode_expansion :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.projectedGround_slice_mode_expansion)
theorem source_actual_projectedGround_slice_mode_expansion : sourceScope_projectedGround_slice_mode_expansion :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.projectedGround_slice_mode_expansion

abbrev sourceScope_chargedPhysicalSourceRow_eq_collision :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.chargedPhysicalSourceRow_eq_collision)
theorem source_actual_chargedPhysicalSourceRow_eq_collision : sourceScope_chargedPhysicalSourceRow_eq_collision :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.chargedPhysicalSourceRow_eq_collision

abbrev sourceScope_chargedPhysicalCollisionRow_tail :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.chargedPhysicalCollisionRow_tail)
theorem source_actual_chargedPhysicalCollisionRow_tail : sourceScope_chargedPhysicalCollisionRow_tail :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.chargedPhysicalCollisionRow_tail

abbrev sourceScope_chargedPhysicalSourceRow_tail :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.chargedPhysicalSourceRow_tail)
theorem source_actual_chargedPhysicalSourceRow_tail : sourceScope_chargedPhysicalSourceRow_tail :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.chargedPhysicalSourceRow_tail

abbrev sourceScope_chargedPhysicalResidueRow_left_finite :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.chargedPhysicalResidueRow_left_finite)
theorem source_actual_chargedPhysicalResidueRow_left_finite : sourceScope_chargedPhysicalResidueRow_left_finite :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.chargedPhysicalResidueRow_left_finite

abbrev sourceScope_chargedPhysicalResidueRow_right_finite :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.chargedPhysicalResidueRow_right_finite)
theorem source_actual_chargedPhysicalResidueRow_right_finite : sourceScope_chargedPhysicalResidueRow_right_finite :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.chargedPhysicalResidueRow_right_finite

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue

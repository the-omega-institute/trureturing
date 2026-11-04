import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints

/-! Exact-source attempt for the same-space signed endpoints. The complete
source telescope is reconstructed below. An enrolled whole-source readout,
selection bridge and whole-family variation/sensitivity are not supplied.
Four-slot registration remains unfinished under issue 21750; no
declared_validated registration is asserted. -/

namespace Reg.D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints.actual_signed_ball_history_endpoints)

theorem exact_source : sourceScope :=
  @_root_.D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints.actual_signed_ball_history_endpoints

end Reg.D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints

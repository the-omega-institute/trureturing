import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalLimit

/-! Exact whole-label source reconstruction is checked. A lawful four-slot
readout and its variation/sensitivity remain unfinished under issue 21750.
No declared_validated registration is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalLimit
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalLimit.Archive

abbrev predecessor_whole_readback_scope := type_of% (@predecessor_whole_readback)
theorem predecessor_whole_readback_source : predecessor_whole_readback_scope :=
  @predecessor_whole_readback

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalLimit

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryState

/-! Exact source reconstruction is checked below. A lawful enrolled readout
and whole-family variation/sensitivity for these dependent actual-history
outputs remain unfinished under issue 21750. No four-slot validation is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryState
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryState

abbrev oldRow_ne_scope := type_of% (@oldRow_ne)
theorem oldRow_ne_source : oldRow_ne_scope := @oldRow_ne

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryState

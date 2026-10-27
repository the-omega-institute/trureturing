import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryEvent

/-! Exact source reconstruction is checked below. A lawful enrolled readout
and whole-family variation/sensitivity for these dependent actual-history
outputs remain unfinished under issue 21750. No four-slot validation is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryEvent
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryEvent

abbrev Event_next_regular_scope := type_of% (@Event.next_regular)
theorem Event_next_regular_source : Event_next_regular_scope := @Event.next_regular

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryEvent

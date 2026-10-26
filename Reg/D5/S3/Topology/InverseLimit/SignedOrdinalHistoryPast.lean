import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryPast

/-! Exact source reconstruction is checked below. A lawful enrolled readout
and whole-family variation/sensitivity for these dependent actual-history
outputs remain unfinished under issue 21750. No four-slot validation is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryPast
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryPast

abbrev carrier_read_scope := type_of% (@carrier_read)
theorem carrier_read_source : carrier_read_scope := @carrier_read

abbrev I_read_scope := type_of% (@I_read)
theorem I_read_source : I_read_scope := @I_read

abbrev J_read_scope := type_of% (@J_read)
theorem J_read_source : J_read_scope := @J_read

abbrev strictLaws_scope := type_of% (@strictLaws)
theorem strictLaws_source : strictLaws_scope := @strictLaws

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryPast

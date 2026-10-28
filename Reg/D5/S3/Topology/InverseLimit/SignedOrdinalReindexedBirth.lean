import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalReindexedBirth

/-! Exact telescopes of whole birth reindexing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalReindexedBirth
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalReindexedBirth

abbrev decode_code_scope := type_of% (@decode_code)
theorem decode_code_source : decode_code_scope := @decode_code

abbrev ordinaryIndex_decode_scope := type_of% (@ordinaryIndex_decode)
theorem ordinaryIndex_decode_source : ordinaryIndex_decode_scope := @ordinaryIndex_decode

abbrev event_read_scope := type_of% (@event_read)
theorem event_read_source : event_read_scope := @event_read

abbrev eventIndex_decode_scope := type_of% (@eventIndex_decode)
theorem eventIndex_decode_source : eventIndex_decode_scope := @eventIndex_decode

abbrev eventIndex_le_scope := type_of% (@eventIndex_le)
theorem eventIndex_le_source : eventIndex_le_scope := @eventIndex_le

abbrev eventIndex_cofinal_scope := type_of% (@eventIndex_cofinal)
theorem eventIndex_cofinal_source : eventIndex_cofinal_scope := @eventIndex_cofinal

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalReindexedBirth

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryPast

/-! Exact source reconstruction is checked. Four-slot realization, lawful
readout and whole-family variation/sensitivity remain unfinished under issue
21750. No declared_validated registration is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryPast
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryPast

abbrev carrier_read_scope := type_of% (@carrier_read)
theorem carrier_read_source : carrier_read_scope := @carrier_read
abbrev bornPack_read_scope := type_of% (@bornPack_read)
theorem bornPack_read_source : bornPack_read_scope := @bornPack_read
abbrev postI_read_scope := type_of% (@postI_read)
theorem postI_read_source : postI_read_scope := @postI_read
abbrev postJ_read_scope := type_of% (@postJ_read)
theorem postJ_read_source : postJ_read_scope := @postJ_read
abbrev postN_read_scope := type_of% (@postN_read)
theorem postN_read_source : postN_read_scope := @postN_read
abbrev postLaws_scope := type_of% (@postLaws)
theorem postLaws_source : postLaws_scope := @postLaws
abbrev I_read_scope := type_of% (@I_read)
theorem I_read_source : I_read_scope := @I_read
abbrev J_read_scope := type_of% (@J_read)
theorem J_read_source : J_read_scope := @J_read
abbrev strictLaws_scope := type_of% (@strictLaws)
theorem strictLaws_source : strictLaws_scope := @strictLaws

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryPast

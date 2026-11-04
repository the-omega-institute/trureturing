import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalHistorySuccessor

/-! Exact source reconstruction is checked below. A lawful enrolled readout
and whole-family variation/sensitivity for these dependent actual-history
outputs remain unfinished under issue 21750. No four-slot validation is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistorySuccessor
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalHistorySuccessor

abbrev next_old_readback_scope := type_of% (@next_old_readback)
theorem next_old_readback_source : next_old_readback_scope := @next_old_readback

abbrev next_coherent_scope := type_of% (@next_coherent)
theorem next_coherent_source : next_coherent_scope := @next_coherent

abbrev next_coherent_earlier_scope := type_of% (@next_coherent_earlier)
theorem next_coherent_earlier_source : next_coherent_earlier_scope := @next_coherent_earlier

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistorySuccessor

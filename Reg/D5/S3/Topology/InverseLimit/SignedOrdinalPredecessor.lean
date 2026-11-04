import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalPredecessor

/-! Exact source reconstruction is checked below. A lawful enrolled readout
and whole-family variation/sensitivity for these dependent actual-history
outputs remain unfinished under issue 21750. No four-slot validation is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalPredecessor
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalPredecessor

abbrev old_carrier_scope := type_of% (@old_carrier)
theorem old_carrier_source : old_carrier_scope := @old_carrier

abbrev next_U_readback_scope := type_of% (@next_U_readback)
theorem next_U_readback_source : next_U_readback_scope := @next_U_readback

abbrev next_V_readback_scope := type_of% (@next_V_readback)
theorem next_V_readback_source : next_V_readback_scope := @next_V_readback

abbrev next_nu_readback_scope := type_of% (@next_nu_readback)
theorem next_nu_readback_source : next_nu_readback_scope := @next_nu_readback

abbrev next_regular_f_scope := type_of% (@next_regular_f)
theorem next_regular_f_source : next_regular_f_scope := @next_regular_f

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalPredecessor

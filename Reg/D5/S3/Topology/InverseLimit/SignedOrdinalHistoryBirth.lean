import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryBirth

/-! Exact source reconstruction is checked below. A lawful enrolled readout
and whole-family variation/sensitivity for these dependent actual-history
outputs remain unfinished under issue 21750. No four-slot validation is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryBirth
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryBirth

abbrev BirthPack_cast_heq_scope := type_of% (@BirthPack.cast_heq)
theorem BirthPack_cast_heq_source : BirthPack_cast_heq_scope := @BirthPack.cast_heq

abbrev BirthPack_cast_B_heq_scope := type_of% (@BirthPack.cast_B_heq)
theorem BirthPack_cast_B_heq_source : BirthPack_cast_B_heq_scope := @BirthPack.cast_B_heq

abbrev BirthPack_heq_V_scope := type_of% (@BirthPack.heq_V)
theorem BirthPack_heq_V_source : BirthPack_heq_V_scope := @BirthPack.heq_V

abbrev BirthPack_heq_measure_scope := type_of% (@BirthPack.heq_measure)
theorem BirthPack_heq_measure_source : BirthPack_heq_measure_scope := @BirthPack.heq_measure

abbrev BirthPack_cast_cast_scope := type_of% (@BirthPack.cast_cast)
theorem BirthPack_cast_cast_source : BirthPack_cast_cast_scope := @BirthPack.cast_cast

abbrev BirthPack_eq_cast_scope := type_of% (@BirthPack.eq_cast)
theorem BirthPack_eq_cast_source : BirthPack_eq_cast_scope := @BirthPack.eq_cast

abbrev prepared_old_readback_scope := type_of% (@prepared_old_readback)
theorem prepared_old_readback_source : prepared_old_readback_scope := @prepared_old_readback

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryBirth

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryTask

/-! Exact source reconstruction is checked below. A lawful enrolled readout
and whole-family variation/sensitivity for these dependent actual-history
outputs remain unfinished under issue 21750. No four-slot validation is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryTask
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryTask

abbrev local_semantics_scope := type_of% (@local_semantics)
theorem local_semantics_source : local_semantics_scope := @local_semantics

abbrev stable_local_scope := type_of% (@stable_local)
theorem stable_local_source : stable_local_scope := @stable_local

abbrev intrinsic_cast_scope := type_of% (@intrinsic_cast)
theorem intrinsic_cast_source : intrinsic_cast_scope := @intrinsic_cast

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryTask

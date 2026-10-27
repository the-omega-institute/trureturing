import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalReindexedLaws

/-! Exact source reconstruction is checked. Four-slot realization, lawful
readout and whole-family variation/sensitivity remain unfinished under issue
21750. No declared_validated registration is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalReindexedLaws
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalReindexedLaws

abbrev properLaws_scope := type_of% (@properLaws)
theorem properLaws_source : properLaws_scope := @properLaws

abbrev nu_read_scope := type_of% (@nu_read)
theorem nu_read_source : nu_read_scope := @nu_read

abbrev nu_reindexBirth_scope := type_of% (@nu_reindexBirth)
theorem nu_reindexBirth_source : nu_reindexBirth_scope := @nu_reindexBirth

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalReindexedLaws

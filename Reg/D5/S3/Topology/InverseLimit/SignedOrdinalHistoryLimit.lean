import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalHistoryLimit

/-! Exact source reconstruction is checked. Four-slot realization, lawful
readout and whole-family variation/sensitivity remain unfinished under issue
21750. No declared_validated registration is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryLimit
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryLimit

abbrev limit_coherent_scope := type_of% (@limit_coherent)
theorem limit_coherent_source : limit_coherent_scope := @limit_coherent

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistoryLimit

import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalRealizationEvents

/-! Exact source reconstruction is checked. Four-slot realization, lawful
readout and whole-family variation/sensitivity remain unfinished under issue
21750. No declared_validated registration is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalRealizationEvents
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalRealizationEvents

abbrev selected_projection_scope := type_of% (@selected_projection)
theorem selected_projection_source : selected_projection_scope := @selected_projection
abbrev successor_J_scope := type_of% (@successor_J)
theorem successor_J_source : successor_J_scope := @successor_J
abbrev ordinary_cofinal_scope := type_of% (@ordinary_cofinal)
theorem ordinary_cofinal_source : ordinary_cofinal_scope := @ordinary_cofinal
abbrev delayed_cofinal_scope := type_of% (@delayed_cofinal)
theorem delayed_cofinal_source : delayed_cofinal_scope := @delayed_cofinal

abbrev prepared_measure_read_scope := type_of% (@prepared_measure_read)
theorem prepared_measure_read_source : prepared_measure_read_scope := @prepared_measure_read

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalRealizationEvents

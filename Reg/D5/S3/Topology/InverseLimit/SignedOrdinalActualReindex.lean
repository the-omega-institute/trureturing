import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalActualReindex

/-! Exact original telescopes for actual selected-event reindexing. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalActualReindex
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalActualReindex

abbrev eventRow_le_scope := type_of% (@eventRow_le)
theorem eventRow_le_source : eventRow_le_scope := @eventRow_le

abbrev eta_le_scope := type_of% (@eta_le)
theorem eta_le_source : eta_le_scope := @eta_le

abbrev selected_target_scope := type_of% (@selected_target)
theorem selected_target_source : selected_target_scope := @selected_target

abbrev selected_measure_scope := type_of% (@selected_measure)
theorem selected_measure_source : selected_measure_scope := @selected_measure

abbrev actual_cofinal_scope := type_of% (@actual_cofinal)
theorem actual_cofinal_source : actual_cofinal_scope := @actual_cofinal

abbrev universal_launch_scope := type_of% (@universal_launch)
theorem universal_launch_source : universal_launch_scope := @universal_launch

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalActualReindex

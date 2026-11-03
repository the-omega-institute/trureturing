import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalDelayed

/-! Exact source reconstruction is checked below. A lawful enrolled readout
and whole-family variation/sensitivity for the dependent same-Result output
remain missing under issue 21750. These are not four-slot registrations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalDelayed

open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor

abbrev delayedScope := type_of% (@exists_delayed_result)
abbrev preparedStepScope := type_of% (@exists_prepared_step)

theorem delayed_source : delayedScope := @exists_delayed_result
theorem prepared_step_source : preparedStepScope := @exists_prepared_step

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalDelayed

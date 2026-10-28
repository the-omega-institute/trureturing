import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.InverseLimit.SignedOrdinalHistory

/-! Exact source reconstruction is checked. Four-slot realization, lawful
readout and whole-family variation/sensitivity remain unfinished under issue
21750. No declared_validated registration is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistory
open _root_.D5.S3.Topology.InverseLimit.SignedOrdinalHistory

abbrev coherent_scope := type_of% (@coherent)
theorem coherent_source : coherent_scope := @coherent
abbrev execution_scope := type_of% (@execution)
theorem execution_source : execution_scope := @execution
abbrev exists_history_scope := type_of% (@exists_history)
theorem exists_history_source : exists_history_scope := @exists_history
abbrev initial_execution_scope := type_of% (@initial_execution)
theorem initial_execution_source : initial_execution_scope := @initial_execution
abbrev successor_execution_scope := type_of% (@successor_execution)
theorem successor_execution_source : successor_execution_scope := @successor_execution
abbrev limit_execution_scope := type_of% (@limit_execution)
theorem limit_execution_source : limit_execution_scope := @limit_execution
abbrev proper_f_scope := type_of% (@proper_f)
theorem proper_f_source : proper_f_scope := @proper_f
abbrev ordinary_cofinal_scope := type_of% (@ordinary_cofinal)
theorem ordinary_cofinal_source : ordinary_cofinal_scope := @ordinary_cofinal
abbrev delayed_cofinal_scope := type_of% (@delayed_cofinal)
theorem delayed_cofinal_source : delayed_cofinal_scope := @delayed_cofinal
abbrev launch_cofinal_scope := type_of% (@launch_cofinal)
theorem launch_cofinal_source : launch_cofinal_scope := @launch_cofinal

abbrev cast_B_eval_scope := type_of% (@cast_B_eval)
theorem cast_B_eval_source : cast_B_eval_scope := @cast_B_eval

end Reg.D5.S3.Topology.InverseLimit.SignedOrdinalHistory

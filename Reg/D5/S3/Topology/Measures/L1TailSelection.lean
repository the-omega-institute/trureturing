import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.L1TailSelection

/-! Exact original source telescopes. Four-slot realization, readout,
reconstruction, variation, sensitivity and observational dependence remain
unfinished; these bindings do not assert a validated registration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.Measures.L1TailSelection

abbrev exists_selection_scope := type_of% (@_root_.D5.S3.Topology.Measures.L1TailSelection.exists_selection)

theorem exists_selection_actual : exists_selection_scope :=
  @_root_.D5.S3.Topology.Measures.L1TailSelection.exists_selection

end Reg.D5.S3.Topology.Measures.L1TailSelection

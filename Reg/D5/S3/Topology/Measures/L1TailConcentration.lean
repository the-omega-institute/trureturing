import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.L1TailConcentration

/-! Exact original source telescopes. Four-slot realization, readout,
reconstruction, variation, sensitivity and observational dependence remain
unfinished; these bindings do not assert a validated registration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.Measures.L1TailConcentration

abbrev eventually_small_cross_tails_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1TailConcentration.eventually_small_cross_tails.{u})

theorem eventually_small_cross_tails_actual.{u} : eventually_small_cross_tails_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1TailConcentration.eventually_small_cross_tails.{u}

abbrev exists_tail_concentration_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1TailConcentration.exists_tail_concentration.{u})

theorem exists_tail_concentration_actual.{u} : exists_tail_concentration_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1TailConcentration.exists_tail_concentration.{u}

end Reg.D5.S3.Topology.Measures.L1TailConcentration

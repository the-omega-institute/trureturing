import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.L1Biting

/-! Exact original source telescopes. Four-slot realization, readout,
reconstruction, variation, sensitivity and observational dependence remain
unfinished; these bindings do not assert a validated registration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.Measures.L1Biting

abbrev uniformIntegrable_complements_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Biting.uniformIntegrable_complements.{u})

theorem uniformIntegrable_complements_actual.{u} : uniformIntegrable_complements_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Biting.uniformIntegrable_complements.{u}

end Reg.D5.S3.Topology.Measures.L1Biting

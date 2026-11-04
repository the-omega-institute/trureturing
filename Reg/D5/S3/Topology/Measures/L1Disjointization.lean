import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.L1Disjointization

/-! Exact original source telescopes. Four-slot realization, readout,
reconstruction, variation, sensitivity and observational dependence remain
unfinished; these bindings do not assert a validated registration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.Measures.L1Disjointization

abbrev exists_disjoint_restrictions_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Disjointization.exists_disjoint_restrictions.{u})

theorem exists_disjoint_restrictions_actual.{u} : exists_disjoint_restrictions_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Disjointization.exists_disjoint_restrictions.{u}

end Reg.D5.S3.Topology.Measures.L1Disjointization

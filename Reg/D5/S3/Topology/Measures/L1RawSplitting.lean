import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.L1RawSplitting

/-! Exact original source telescopes. Four-slot realization, readout,
reconstruction, variation, sensitivity and observational dependence remain
unfinished; these bindings do not assert a validated registration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.Measures.L1RawSplitting

abbrev exists_raw_restriction_splitting_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1RawSplitting.exists_raw_restriction_splitting.{u})

theorem exists_raw_restriction_splitting_actual.{u} : exists_raw_restriction_splitting_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1RawSplitting.exists_raw_restriction_splitting.{u}

end Reg.D5.S3.Topology.Measures.L1RawSplitting

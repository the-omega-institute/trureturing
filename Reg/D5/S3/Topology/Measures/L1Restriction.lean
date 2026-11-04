import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.L1Restriction

/-! Exact original source telescopes. Four-slot realization, readout,
reconstruction, variation, sensitivity and observational dependence remain
unfinished; these bindings do not assert a validated registration. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.Measures.L1Restriction

abbrev coe_restrict_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Restriction.coe_restrict.{u})

theorem coe_restrict_actual.{u} : coe_restrict_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Restriction.coe_restrict.{u}

abbrev norm_restrict_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Restriction.norm_restrict.{u})

theorem norm_restrict_actual.{u} : norm_restrict_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Restriction.norm_restrict.{u}

abbrev enorm_restrict_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Restriction.enorm_restrict.{u})

theorem enorm_restrict_actual.{u} : enorm_restrict_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Restriction.enorm_restrict.{u}

abbrev add_compl_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Restriction.add_compl.{u})

theorem add_compl_actual.{u} : add_compl_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Restriction.add_compl.{u}

abbrev norm_add_compl_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Restriction.norm_add_compl.{u})

theorem norm_add_compl_actual.{u} : norm_add_compl_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Restriction.norm_add_compl.{u}

abbrev norm_le_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Restriction.norm_le.{u})

theorem norm_le_actual.{u} : norm_le_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Restriction.norm_le.{u}

abbrev norm_mono_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Restriction.norm_mono.{u})

theorem norm_mono_actual.{u} : norm_mono_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Restriction.norm_mono.{u}

abbrev measurable_tailSet_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Restriction.measurable_tailSet.{u})

theorem measurable_tailSet_actual.{u} : measurable_tailSet_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Restriction.measurable_tailSet.{u}

abbrev tailNorm_antitone_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Restriction.tailNorm_antitone.{u})

theorem tailNorm_antitone_actual.{u} : tailNorm_antitone_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Restriction.tailNorm_antitone.{u}

abbrev tailNorm_compl_scope.{u} := type_of% (@_root_.D5.S3.Topology.Measures.L1Restriction.tailNorm_compl.{u})

theorem tailNorm_compl_actual.{u} : tailNorm_compl_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.L1Restriction.tailNorm_compl.{u}

end Reg.D5.S3.Topology.Measures.L1Restriction

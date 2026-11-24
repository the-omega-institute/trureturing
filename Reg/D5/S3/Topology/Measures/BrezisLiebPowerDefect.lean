module

public import D5.S3.Topology.Measures.BrezisLiebPowerDefect

/-! # Exact source telescope

The source binding preserves every universe, measure, complex scalar, exponent,
measurability, mass and conclusion clause. It asserts no four-slot registration.
The unfinished dependent-family realization and source-observation binding are
tracked in https://github.com/the-omega-institute/trureturing/issues/33684.
-/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.Measures.BrezisLiebPowerDefect

universe u

abbrev source_scope := type_of%
  (@_root_.D5.S3.Topology.Measures.BrezisLiebPowerDefect.brezis_lieb_power_defect.{u})

theorem source_actual : source_scope.{u} :=
  @_root_.D5.S3.Topology.Measures.BrezisLiebPowerDefect.brezis_lieb_power_defect.{u}

#print axioms source_actual

end Reg.D5.S3.Topology.Measures.BrezisLiebPowerDefect

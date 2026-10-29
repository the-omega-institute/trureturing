import D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMobile

/-! Source-owned mirror for the exact mobile result.

The original theorem is retained exactly. A lawful four-slot source registration
is unfinished because the current dependent-family observation template does
not yet provide a faithful readout for the Prop-valued mobile predicate and
its universal-plus-existential result. The linked issue records the missing
binding evidence; this mirror does not claim declared_validated status.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMobile

abbrev result_scope :=
  type_of% (@D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMobile.result)

theorem result_source : result_scope :=
  @D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMobile.result

end Reg.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeMobile

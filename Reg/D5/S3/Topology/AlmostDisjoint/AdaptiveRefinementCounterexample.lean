import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample

namespace Reg.D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample

open _root_.D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample

/-- The entire existential source statement is checked, including the literal
open two-set cover, arbitrary finite closed refinements with repeated labels and
the absence of a compact Hausdorff zero-dimensional open resolution.
Whole-source variation and raw occurrence reconstruction/sourceSelection remain
unfinished under the linked issue; this is not a validated four-slot registration. -/
abbrev sourceScope := type_of% (@exists_compact_open_map_no_finite_closed_refinement)

theorem source_actual : sourceScope :=
  @exists_compact_open_map_no_finite_closed_refinement

end Reg.D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample

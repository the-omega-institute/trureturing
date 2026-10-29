import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.SphereOrthogonalityCover

/-!
Exact theorem telescopes and source proofs are retained below. Four-slot
registration is incomplete: the dependent-family template still needs a
whole-source arena for the cover, topology and varying dimension, an enrolled
readout and sourceSelection, a realization-equivalence bridge, whole-family
variation and sensitivity, and actual observational dependence.
No declared_validated registration is claimed. The linked-issue exception
is tracked at https://github.com/the-omega-institute/trureturing/issues/23716.
-/

namespace Reg.D5.S3.Topology.SphereOrthogonalityCover

abbrev component_inner_pos_scope := type_of%
  (@_root_.D5.S3.Topology.SphereOrthogonalityCover.component_inner_pos)
theorem component_inner_pos_source : component_inner_pos_scope :=
  @_root_.D5.S3.Topology.SphereOrthogonalityCover.component_inner_pos

abbrev cover_color_multiplicity_scope := type_of%
  (@_root_.D5.S3.Topology.SphereOrthogonalityCover.cover_color_multiplicity)
theorem cover_color_multiplicity_source : cover_color_multiplicity_scope :=
  @_root_.D5.S3.Topology.SphereOrthogonalityCover.cover_color_multiplicity

abbrev exists_finite_acute_refinement_scope := type_of%
  (@_root_.D5.S3.Topology.SphereOrthogonalityCover.exists_finite_acute_refinement)
theorem exists_finite_acute_refinement_source : exists_finite_acute_refinement_scope :=
  @_root_.D5.S3.Topology.SphereOrthogonalityCover.exists_finite_acute_refinement

abbrev acute_cover_normalized_map_scope := type_of%
  (@_root_.D5.S3.Topology.SphereOrthogonalityCover.acute_cover_normalized_map)
theorem acute_cover_normalized_map_source : acute_cover_normalized_map_scope :=
  @_root_.D5.S3.Topology.SphereOrthogonalityCover.acute_cover_normalized_map

abbrev map_omits_point_of_small_spans_scope := type_of%
  (@_root_.D5.S3.Topology.SphereOrthogonalityCover.map_omits_point_of_small_spans)
theorem map_omits_point_of_small_spans_source : map_omits_point_of_small_spans_scope :=
  @_root_.D5.S3.Topology.SphereOrthogonalityCover.map_omits_point_of_small_spans

abbrev acute_cover_contractible_of_multiplicity_lt_scope := type_of%
  (@_root_.D5.S3.Topology.SphereOrthogonalityCover.acute_cover_contractible_of_multiplicity_lt)
theorem acute_cover_contractible_of_multiplicity_lt_source : acute_cover_contractible_of_multiplicity_lt_scope :=
  @_root_.D5.S3.Topology.SphereOrthogonalityCover.acute_cover_contractible_of_multiplicity_lt

abbrev open_cover_contractible_of_multiplicity_lt_scope := type_of%
  (@_root_.D5.S3.Topology.SphereOrthogonalityCover.open_cover_contractible_of_multiplicity_lt)
theorem open_cover_contractible_of_multiplicity_lt_source : open_cover_contractible_of_multiplicity_lt_scope :=
  @_root_.D5.S3.Topology.SphereOrthogonalityCover.open_cover_contractible_of_multiplicity_lt

abbrev low_color_cover_contractible_scope := type_of%
  (@_root_.D5.S3.Topology.SphereOrthogonalityCover.low_color_cover_contractible)
theorem low_color_cover_contractible_source : low_color_cover_contractible_scope :=
  @_root_.D5.S3.Topology.SphereOrthogonalityCover.low_color_cover_contractible

abbrev sphere_open_orthogonality_free_cover_lower_bound_scope := type_of%
  (@_root_.D5.S3.Topology.SphereOrthogonalityCover.sphere_open_orthogonality_free_cover_lower_bound)
theorem sphere_open_orthogonality_free_cover_lower_bound_source : sphere_open_orthogonality_free_cover_lower_bound_scope :=
  @_root_.D5.S3.Topology.SphereOrthogonalityCover.sphere_open_orthogonality_free_cover_lower_bound

abbrev sphere_three_absent_colors_scope := type_of%
  (@_root_.D5.S3.Topology.SphereOrthogonalityCover.sphere_three_absent_colors)
theorem sphere_three_absent_colors_source : sphere_three_absent_colors_scope :=
  @_root_.D5.S3.Topology.SphereOrthogonalityCover.sphere_three_absent_colors

abbrev sphere_two_open_orthogonality_free_cover_lower_six_scope := type_of%
  (@_root_.D5.S3.Topology.SphereOrthogonalityCover.sphere_two_open_orthogonality_free_cover_lower_six)
theorem sphere_two_open_orthogonality_free_cover_lower_six_source : sphere_two_open_orthogonality_free_cover_lower_six_scope :=
  @_root_.D5.S3.Topology.SphereOrthogonalityCover.sphere_two_open_orthogonality_free_cover_lower_six

end Reg.D5.S3.Topology.SphereOrthogonalityCover

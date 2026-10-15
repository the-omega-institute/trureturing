import D5.S1.Dynamics.Shadowing.MetricTracing

namespace Reg.D5.S1.Dynamics.Shadowing.MetricTracing

universe u

/- The complete original telescopes are preserved as typed expressions.
Four-slot realization, source reconstruction, whole-family sensitivity,
observational dependence and enrolled readout binding remain unresolved.
The original infinite domains and all natural tracing times remain in scope.
The existing coordination issue is
https://github.com/the-omega-institute/trureturing/issues/5214.
These expressions supply no Contract.Registration or declared_validated evidence. -/

abbrev metric_shadowing_iff_uniform_scope := type_of%
  (@_root_.D5.S1.Dynamics.Shadowing.metric_shadowing_iff_uniform.{u})
theorem metric_shadowing_iff_uniform_actual : metric_shadowing_iff_uniform_scope.{u} :=
  @_root_.D5.S1.Dynamics.Shadowing.metric_shadowing_iff_uniform.{u}

abbrev lipschitz_ordinary_scope := type_of%
  (@_root_.D5.S1.Dynamics.Shadowing.HasLipschitzShadowing.metricHasShadowing.{u})
theorem lipschitz_ordinary_actual : lipschitz_ordinary_scope.{u} :=
  @_root_.D5.S1.Dynamics.Shadowing.HasLipschitzShadowing.metricHasShadowing.{u}

abbrev shift_one_iterate_apply_scope := type_of%
  (@_root_.D5.S1.Dynamics.Shadowing.shift_one_iterate_apply.{u})
theorem shift_one_iterate_apply_actual : shift_one_iterate_apply_scope.{u} :=
  @_root_.D5.S1.Dynamics.Shadowing.shift_one_iterate_apply.{u}

abbrev diagonal_splice_overlap_scope := type_of%
  (@_root_.D5.S1.Dynamics.Shadowing.diagonal_splice_overlap.{u})
theorem diagonal_splice_overlap_actual : diagonal_splice_overlap_scope.{u} :=
  @_root_.D5.S1.Dynamics.Shadowing.diagonal_splice_overlap.{u}

abbrev diagonal_mismatch_edge_scope := type_of%
  (@_root_.D5.S1.Dynamics.Shadowing.diagonal_mismatch_edge.{u})
theorem diagonal_mismatch_edge_actual : diagonal_mismatch_edge_scope.{u} :=
  @_root_.D5.S1.Dynamics.Shadowing.diagonal_mismatch_edge.{u}

end Reg.D5.S1.Dynamics.Shadowing.MetricTracing

import D5.S1.Dynamics.Shadowing.HeadWeightedLipschitz

/-! Complete telescope checks for the head-weight Lipschitz criterion. -/

namespace Reg.D5.S1.Dynamics.Shadowing.HeadWeightedLipschitz

/- The full original telescopes are preserved. The arbitrary head-weight
family, all positive controls below the cutoff, infinite pseudo-orbits and
all natural tracing times remain in scope. Four-slot realization and source
reconstruction are not asserted. The existing coordination issue is
https://github.com/the-omega-institute/trureturing/issues/5214.
These expressions supply no Contract.Registration or declared_validated evidence. -/

abbrev diagonal_traces_of_adjacent_ratio_scope := type_of%
  (@_root_.D5.S1.Dynamics.Shadowing.HeadWeights.diagonal_traces_of_adjacent_ratio)
theorem diagonal_traces_of_adjacent_ratio_actual : diagonal_traces_of_adjacent_ratio_scope :=
  @_root_.D5.S1.Dynamics.Shadowing.HeadWeights.diagonal_traces_of_adjacent_ratio

abbrev rawMetric_hasLipschitzShadowing_iff_adjacent_ratio_scope := type_of%
  (@_root_.D5.S1.Dynamics.Shadowing.HeadWeights.rawMetric_hasLipschitzShadowing_iff_adjacent_ratio)
theorem rawMetric_hasLipschitzShadowing_iff_adjacent_ratio_actual :
    rawMetric_hasLipschitzShadowing_iff_adjacent_ratio_scope :=
  @_root_.D5.S1.Dynamics.Shadowing.HeadWeights.rawMetric_hasLipschitzShadowing_iff_adjacent_ratio

end Reg.D5.S1.Dynamics.Shadowing.HeadWeightedLipschitz

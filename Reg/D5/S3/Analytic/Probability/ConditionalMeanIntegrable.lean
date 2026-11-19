import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport
import D5.S3.Analytic.Probability.ConditionalMeanIntegrable

/-! Typed source-law reconstruction for integrable quantile-bin results. -/

open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit

noncomputable section
namespace Reg.D5.S3.Analytic.Probability.ConditionalMeanIntegrable

namespace upperIntegratedQuantile_le_of_stopLoss_le
abbrev arena : Arena where
  signature := Quantile
  Law r := source_law% Econlib.Probability.upperIntegratedQuantile_le_of_stopLoss_le
    replacing (@MeasureTheory.Measure.quantile) with (r.readout ())

theorem source_bridge : (type_of% @Econlib.Probability.upperIntegratedQuantile_le_of_stopLoss_le) ↔
    arena.Law quantileActual := Iff.rfl

theorem actual_law : arena.Law quantileActual :=
  source_bridge.mp @Econlib.Probability.upperIntegratedQuantile_le_of_stopLoss_le
end upperIntegratedQuantile_le_of_stopLoss_le

namespace lowerIntegratedQuantile_ge_of_upper_le
abbrev arena : Arena where
  signature := Quantile
  Law r := source_law% Econlib.Probability.lowerIntegratedQuantile_ge_of_upper_le
    replacing (@MeasureTheory.Measure.quantile) with (r.readout ())

theorem source_bridge : (type_of% @Econlib.Probability.lowerIntegratedQuantile_ge_of_upper_le) ↔
    arena.Law quantileActual := Iff.rfl

theorem actual_law : arena.Law quantileActual :=
  source_bridge.mp @Econlib.Probability.lowerIntegratedQuantile_ge_of_upper_le
end lowerIntegratedQuantile_ge_of_upper_le

namespace integrableOn_quantile_bin_of_integrable
abbrev arena : Arena where
  signature := Quantile
  Law r := source_law% Econlib.Probability.DiscreteLaw.integrableOn_quantile_bin_of_integrable
    replacing (@MeasureTheory.Measure.quantile) with (r.readout ())

theorem source_bridge :
    (type_of% @Econlib.Probability.DiscreteLaw.integrableOn_quantile_bin_of_integrable) ↔
      arena.Law quantileActual := Iff.rfl

theorem actual_law : arena.Law quantileActual :=
  source_bridge.mp @Econlib.Probability.DiscreteLaw.integrableOn_quantile_bin_of_integrable
end integrableOn_quantile_bin_of_integrable

namespace condMeanAtom_monotone_of_integrable_bins
abbrev arena : Arena where
  signature := Atom
  Law r := source_law% Econlib.Probability.DiscreteLaw.condMeanAtom_monotone_of_integrable_bins
    replacing (@DiscreteLaw.condMeanAtom) with (fun μ n hn k => r.readout () ⟨μ, n, ⟨hn⟩⟩ k)

theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.condMeanAtom_monotone_of_integrable_bins) ↔
    arena.Law atomActual := Iff.rfl

theorem actual_law : arena.Law atomActual :=
  source_bridge.mp @Econlib.Probability.DiscreteLaw.condMeanAtom_monotone_of_integrable_bins
end condMeanAtom_monotone_of_integrable_bins

namespace condMeanAtomize_partial_sum_eq_of_integrable_bins
abbrev arena : Arena where
  signature := Atom
  Law r := source_law% Econlib.Probability.DiscreteLaw.condMeanAtomize_partial_sum_eq_of_integrable_bins
    replacing (@DiscreteLaw.condMeanAtom) with (fun μ n hn k => r.readout () ⟨μ, n, ⟨hn⟩⟩ k)

theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.condMeanAtomize_partial_sum_eq_of_integrable_bins) ↔
    arena.Law atomActual := Iff.rfl

theorem actual_law : arena.Law atomActual :=
  source_bridge.mp @Econlib.Probability.DiscreteLaw.condMeanAtomize_partial_sum_eq_of_integrable_bins
end condMeanAtomize_partial_sum_eq_of_integrable_bins

namespace condMeanAtomize_tendsto_of_integrable_bins
abbrev arena : Arena where
  signature := Atomization
  Law r := source_law% Econlib.Probability.DiscreteLaw.condMeanAtomize_tendsto_of_integrable_bins
    replacing (@DiscreteLaw.condMeanAtomize) with (fun μ n hn => r.readout () μ ⟨n, hn⟩)

theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.condMeanAtomize_tendsto_of_integrable_bins) ↔
    arena.Law atomizationActual := Iff.rfl

theorem actual_law : arena.Law atomizationActual :=
  source_bridge.mp @Econlib.Probability.DiscreteLaw.condMeanAtomize_tendsto_of_integrable_bins
end condMeanAtomize_tendsto_of_integrable_bins

namespace condMeanAtomize_convexOrder_of_lowerIntegratedQuantile
abbrev arena : Arena where
  signature := Atomization
  Law r := source_law% Econlib.Probability.DiscreteLaw.condMeanAtomize_convexOrder_of_lowerIntegratedQuantile
    replacing (@DiscreteLaw.condMeanAtomize) with (fun μ n hn => r.readout () μ ⟨n, hn⟩)

theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.condMeanAtomize_convexOrder_of_lowerIntegratedQuantile) ↔
    arena.Law atomizationActual := Iff.rfl

theorem actual_law : arena.Law atomizationActual :=
  source_bridge.mp @Econlib.Probability.DiscreteLaw.condMeanAtomize_convexOrder_of_lowerIntegratedQuantile
end condMeanAtomize_convexOrder_of_lowerIntegratedQuantile

end Reg.D5.S3.Analytic.Probability.ConditionalMeanIntegrable
end

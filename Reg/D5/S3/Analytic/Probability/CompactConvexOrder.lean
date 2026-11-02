import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport

/-! Typed source-law reconstruction for compact martingale transport. -/
open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit
noncomputable section
universe u_1 u_2
namespace Reg.D5.S3.Analytic.Probability.CompactConvexOrder



namespace ae_mem_of_supportsOn
abbrev arena : Arena where
  signature := Support
  Law r := source_law% Econlib.Probability.ProbDist.ae_mem_of_supportsOn replacing (@ProbDist.supportsOn ℝ inferInstance) with (r.readout ())
theorem source_bridge : (type_of% @Econlib.Probability.ProbDist.ae_mem_of_supportsOn) ↔ arena.Law supportActual := Iff.rfl
theorem actual_law : arena.Law supportActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.ProbDist.ae_mem_of_supportsOn
end ae_mem_of_supportsOn

namespace integrable_of_supportsOn_Icc
abbrev arena : Arena where
  signature := Support
  Law r := source_law% Econlib.Probability.ProbDist.integrable_of_supportsOn_Icc replacing (@ProbDist.supportsOn ℝ inferInstance) with (r.readout ())
theorem source_bridge : (type_of% @Econlib.Probability.ProbDist.integrable_of_supportsOn_Icc) ↔ arena.Law supportActual := Iff.rfl
theorem actual_law : arena.Law supportActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.ProbDist.integrable_of_supportsOn_Icc
end integrable_of_supportsOn_Icc

namespace integrable_id_of_supportsOn_Icc
abbrev arena : Arena where
  signature := Support
  Law r := source_law% Econlib.Probability.ProbDist.integrable_id_of_supportsOn_Icc replacing (@ProbDist.supportsOn ℝ inferInstance) with (r.readout ())
theorem source_bridge : (type_of% @Econlib.Probability.ProbDist.integrable_id_of_supportsOn_Icc) ↔ arena.Law supportActual := Iff.rfl
theorem actual_law : arena.Law supportActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.ProbDist.integrable_id_of_supportsOn_Icc
end integrable_id_of_supportsOn_Icc

namespace lowerIntegratedQuantile_ge_of_convexOrderOnIcc
abbrev arena : Arena where
  signature := Quantile
  Law r := source_law% Econlib.Probability.lowerIntegratedQuantile_ge_of_convexOrderOnIcc replacing (@MeasureTheory.Measure.quantile) with (r.readout ())
theorem source_bridge : (type_of% @Econlib.Probability.lowerIntegratedQuantile_ge_of_convexOrderOnIcc) ↔ arena.Law quantileActual := Iff.rfl
theorem actual_law : arena.Law quantileActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.lowerIntegratedQuantile_ge_of_convexOrderOnIcc
end lowerIntegratedQuantile_ge_of_convexOrderOnIcc
end Reg.D5.S3.Analytic.Probability.CompactConvexOrder
end

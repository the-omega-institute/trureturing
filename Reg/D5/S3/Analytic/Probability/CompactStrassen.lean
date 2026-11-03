import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport

/-! Typed source-law reconstruction for compact martingale transport. -/
open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit
noncomputable section
universe u_1 u_2
namespace Reg.D5.S3.Analytic.Probability.CompactStrassen

namespace tested_martingale_of_weak_limit
abbrev arena : Arena where
  signature := JointMeasure
  Law r := source_law% Econlib.Probability.tested_martingale_of_weak_limit replacing (@ProbabilityMeasure.toMeasure (ℝ × ℝ) inferInstance) with (r.readout () ())
theorem source_bridge : (type_of% @Econlib.Probability.tested_martingale_of_weak_limit) ↔ arena.Law jointMeasureActual := Iff.rfl
theorem actual_law : arena.Law jointMeasureActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.tested_martingale_of_weak_limit
end tested_martingale_of_weak_limit

namespace tested_martingale_measurable_of_continuous
abbrev arena : Arena where
  signature := JointMeasure
  Law r := source_law% Econlib.Probability.tested_martingale_measurable_of_continuous replacing (@ProbabilityMeasure.toMeasure (ℝ × ℝ) inferInstance) with (r.readout () ())
theorem source_bridge : (type_of% @Econlib.Probability.tested_martingale_measurable_of_continuous) ↔ arena.Law jointMeasureActual := Iff.rfl
theorem actual_law : arena.Law jointMeasureActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.tested_martingale_measurable_of_continuous
end tested_martingale_measurable_of_continuous

namespace martingaleCoupling_of_weak_limit
abbrev arena : Arena where
  signature := Coupling
  Law r := source_law% Econlib.Probability.IsMartingaleCoupling.martingaleCoupling_of_weak_limit replacing (@IsMartingaleCoupling) with (fun μ ν π => r.readout () (μ, ν) π)
theorem source_bridge : (type_of% @Econlib.Probability.IsMartingaleCoupling.martingaleCoupling_of_weak_limit) ↔ arena.Law martingaleActual := Iff.rfl
theorem actual_law : arena.Law martingaleActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.IsMartingaleCoupling.martingaleCoupling_of_weak_limit
end martingaleCoupling_of_weak_limit

namespace compact_convex_order_iff_martingale
abbrev arena : Arena where
  signature := ScalarMeasure
  Law r := source_law% Econlib.Probability.compact_convex_order_iff_martingale replacing (@ProbabilityMeasure.toMeasure ℝ inferInstance) with (r.readout () ())
theorem source_bridge : (type_of% @Econlib.Probability.compact_convex_order_iff_martingale) ↔ arena.Law scalarMeasureActual := Iff.rfl
theorem actual_law : arena.Law scalarMeasureActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.compact_convex_order_iff_martingale
end compact_convex_order_iff_martingale
end Reg.D5.S3.Analytic.Probability.CompactStrassen
end

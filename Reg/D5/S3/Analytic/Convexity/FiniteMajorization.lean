import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport

/-! Typed source-law reconstruction for compact martingale transport. -/
open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit
noncomputable section
universe u_1 u_2
namespace Reg.D5.S3.Analytic.Convexity.FiniteMajorization

namespace convexOn_hinge_right
abbrev arena : Arena where
  signature := Max
  Law r := source_law% convexOn_hinge_right replacing (max : ℝ → ℝ → ℝ) with (r.readout ())
theorem source_bridge : (type_of% @convexOn_hinge_right) ↔ arena.Law maxActual := Iff.rfl
theorem actual_law : arena.Law maxActual := by
  apply source_bridge.mp
  exact @convexOn_hinge_right
end convexOn_hinge_right

namespace exists_doublyStochastic_mulVec_of_convex_dominates
abbrev arena : Arena where
  signature := Convex
  Law r := source_law% exists_doublyStochastic_mulVec_of_convex_dominates replacing (ConvexOn ℝ Set.univ : (ℝ → ℝ) → Prop) with (r.readout () ())
theorem source_bridge : (type_of% @exists_doublyStochastic_mulVec_of_convex_dominates) ↔ arena.Law convexActual := Iff.rfl
theorem actual_law : arena.Law convexActual := by
  apply source_bridge.mp
  exact @exists_doublyStochastic_mulVec_of_convex_dominates
end exists_doublyStochastic_mulVec_of_convex_dominates

namespace sum_convex_le_of_partial_sum_ge
abbrev arena : Arena where
  signature := Convex
  Law r := source_law% sum_convex_le_of_partial_sum_ge replacing (ConvexOn ℝ Set.univ : (ℝ → ℝ) → Prop) with (r.readout () ())
theorem source_bridge : (type_of% @sum_convex_le_of_partial_sum_ge) ↔ arena.Law convexActual := Iff.rfl
theorem actual_law : arena.Law convexActual := by
  apply source_bridge.mp
  exact @sum_convex_le_of_partial_sum_ge
end sum_convex_le_of_partial_sum_ge
end Reg.D5.S3.Analytic.Convexity.FiniteMajorization
end

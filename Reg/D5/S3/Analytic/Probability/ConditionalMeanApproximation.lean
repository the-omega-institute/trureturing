import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport

/-! Typed source-law reconstruction for compact martingale transport. -/
open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit
noncomputable section
universe u_1 u_2
namespace Reg.D5.S3.Analytic.Probability.ConditionalMeanApproximation

namespace condMeanAtomize_tendsto
abbrev arena : Arena where
  signature := Atomization
  Law r := source_law% Econlib.Probability.DiscreteLaw.condMeanAtomize_tendsto replacing (@DiscreteLaw.condMeanAtomize) with (fun μ n hn => r.readout () μ ⟨n, hn⟩)
theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.condMeanAtomize_tendsto) ↔ arena.Law atomizationActual := Iff.rfl
theorem actual_law : arena.Law atomizationActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.DiscreteLaw.condMeanAtomize_tendsto
end condMeanAtomize_tendsto

namespace condMeanAtomize_convexOrder
abbrev arena : Arena where
  signature := Atomization
  Law r := source_law% Econlib.Probability.DiscreteLaw.condMeanAtomize_convexOrder replacing (@DiscreteLaw.condMeanAtomize) with (fun μ n hn => r.readout () μ ⟨n, hn⟩)
theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.condMeanAtomize_convexOrder) ↔ arena.Law atomizationActual := Iff.rfl
theorem actual_law : arena.Law atomizationActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.DiscreteLaw.condMeanAtomize_convexOrder
end condMeanAtomize_convexOrder

namespace exists_discrete_approximation
abbrev arena : Arena where
  signature := FiniteLaw
  Law r := source_law% Econlib.Probability.exists_discrete_approximation replacing (@DiscreteLaw.toProbDist) with (r.readout () ())
theorem source_bridge : (type_of% @Econlib.Probability.exists_discrete_approximation) ↔ arena.Law finiteLawActual := Iff.rfl
theorem actual_law : arena.Law finiteLawActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.exists_discrete_approximation
end exists_discrete_approximation
end Reg.D5.S3.Analytic.Probability.ConditionalMeanApproximation
end

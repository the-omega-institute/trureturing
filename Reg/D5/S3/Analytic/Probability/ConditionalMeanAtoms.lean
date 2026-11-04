import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport

/-! Typed source-law reconstruction for compact martingale transport. -/
open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit
noncomputable section
universe u_1 u_2
namespace Reg.D5.S3.Analytic.Probability.ConditionalMeanAtoms

namespace integrableOn_quantile_bin
abbrev arena : Arena where
  signature := Quantile
  Law r := source_law% Econlib.Probability.DiscreteLaw.integrableOn_quantile_bin replacing (@MeasureTheory.Measure.quantile) with (r.readout ())
theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.integrableOn_quantile_bin) ↔ arena.Law quantileActual := Iff.rfl
theorem actual_law : arena.Law quantileActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.DiscreteLaw.integrableOn_quantile_bin
end integrableOn_quantile_bin

namespace condMeanAtom_mem_Icc
abbrev arena : Arena where
  signature := Atom
  Law r := source_law% Econlib.Probability.DiscreteLaw.condMeanAtom_mem_Icc replacing (@DiscreteLaw.condMeanAtom) with (fun μ n hn k => r.readout () ⟨μ, n, ⟨hn⟩⟩ k)
theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.condMeanAtom_mem_Icc) ↔ arena.Law atomActual := Iff.rfl
theorem actual_law : arena.Law atomActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.DiscreteLaw.condMeanAtom_mem_Icc
end condMeanAtom_mem_Icc

namespace condMeanAtom_monotone
abbrev arena : Arena where
  signature := Atom
  Law r := source_law% Econlib.Probability.DiscreteLaw.condMeanAtom_monotone replacing (@DiscreteLaw.condMeanAtom) with (fun μ n hn k => r.readout () ⟨μ, n, ⟨hn⟩⟩ k)
theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.condMeanAtom_monotone) ↔ arena.Law atomActual := Iff.rfl
theorem actual_law : arena.Law atomActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.DiscreteLaw.condMeanAtom_monotone
end condMeanAtom_monotone

namespace condMeanAtomize_mean_eq
abbrev arena : Arena where
  signature := Atomization
  Law r := source_law% Econlib.Probability.DiscreteLaw.condMeanAtomize_mean_eq replacing (@DiscreteLaw.condMeanAtomize) with (fun μ n hn => r.readout () μ ⟨n, hn⟩)
theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.condMeanAtomize_mean_eq) ↔ arena.Law atomizationActual := Iff.rfl
theorem actual_law : arena.Law atomizationActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.DiscreteLaw.condMeanAtomize_mean_eq
end condMeanAtomize_mean_eq

namespace condMeanAtomize_partial_sum_eq
abbrev arena : Arena where
  signature := Atom
  Law r := source_law% Econlib.Probability.DiscreteLaw.condMeanAtomize_partial_sum_eq replacing (@DiscreteLaw.condMeanAtom) with (fun μ n hn k => r.readout () ⟨μ, n, ⟨hn⟩⟩ k)
theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.condMeanAtomize_partial_sum_eq) ↔ arena.Law atomActual := Iff.rfl
theorem actual_law : arena.Law atomActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.DiscreteLaw.condMeanAtomize_partial_sum_eq
end condMeanAtomize_partial_sum_eq
end Reg.D5.S3.Analytic.Probability.ConditionalMeanAtoms
end

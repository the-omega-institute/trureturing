import Reg.D5.S3.Analytic.Probability.CompactStrassenAuditSupport

/-! Typed source-law reconstruction for compact martingale transport. -/
open MeasureTheory Set Econlib.Probability
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.CompactStrassenAudit
noncomputable section
universe u_1 u_2
namespace Reg.D5.S3.Analytic.Probability.FiniteMartingaleCoupling

namespace fst_probability_marginal
abbrev arena : Arena where
  signature := Coupling
  Law r := source_law% Econlib.Probability.IsCoupling.fst_probability_marginal replacing (@IsCoupling ℝ ℝ inferInstance inferInstance) with (fun μ ν π => r.readout () (μ, ν) π)
theorem source_bridge : (type_of% @Econlib.Probability.IsCoupling.fst_probability_marginal) ↔ arena.Law couplingActual := Iff.rfl
theorem actual_law : arena.Law couplingActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.IsCoupling.fst_probability_marginal
end fst_probability_marginal

namespace snd_probability_marginal
abbrev arena : Arena where
  signature := Coupling
  Law r := source_law% Econlib.Probability.IsCoupling.snd_probability_marginal replacing (@IsCoupling ℝ ℝ inferInstance inferInstance) with (fun μ ν π => r.readout () (μ, ν) π)
theorem source_bridge : (type_of% @Econlib.Probability.IsCoupling.snd_probability_marginal) ↔ arena.Law couplingActual := Iff.rfl
theorem actual_law : arena.Law couplingActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.IsCoupling.snd_probability_marginal
end snd_probability_marginal

namespace supportsOn_Icc_prod
abbrev arena : Arena where
  signature := Coupling
  Law r := source_law% Econlib.Probability.IsCoupling.supportsOn_Icc_prod replacing (@IsCoupling ℝ ℝ inferInstance inferInstance) with (fun μ ν π => r.readout () (μ, ν) π)
theorem source_bridge : (type_of% @Econlib.Probability.IsCoupling.supportsOn_Icc_prod) ↔ arena.Law couplingActual := Iff.rfl
theorem actual_law : arena.Law couplingActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.IsCoupling.supportsOn_Icc_prod
end supportsOn_Icc_prod

namespace fst_measure
abbrev arena : Arena where
  signature := Coupling
  Law r := source_law% Econlib.Probability.IsMartingaleCoupling.fst_measure replacing (@IsMartingaleCoupling) with (fun μ ν π => r.readout () (μ, ν) π)
theorem source_bridge : (type_of% @Econlib.Probability.IsMartingaleCoupling.fst_measure) ↔ arena.Law martingaleActual := Iff.rfl
theorem actual_law : arena.Law martingaleActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.IsMartingaleCoupling.fst_measure
end fst_measure

namespace snd_measure
abbrev arena : Arena where
  signature := Coupling
  Law r := source_law% Econlib.Probability.IsMartingaleCoupling.snd_measure replacing (@IsMartingaleCoupling) with (fun μ ν π => r.readout () (μ, ν) π)
theorem source_bridge : (type_of% @Econlib.Probability.IsMartingaleCoupling.snd_measure) ↔ arena.Law martingaleActual := Iff.rfl
theorem actual_law : arena.Law martingaleActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.IsMartingaleCoupling.snd_measure
end snd_measure

namespace marginal_mean_eq
abbrev arena : Arena where
  signature := Coupling
  Law r := source_law% Econlib.Probability.IsMartingaleCoupling.marginal_mean_eq replacing (@IsMartingaleCoupling) with (fun μ ν π => r.readout () (μ, ν) π)
theorem source_bridge : (type_of% @Econlib.Probability.IsMartingaleCoupling.marginal_mean_eq) ↔ arena.Law martingaleActual := Iff.rfl
theorem actual_law : arena.Law martingaleActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.IsMartingaleCoupling.marginal_mean_eq
end marginal_mean_eq

namespace convex_expect_le
abbrev arena : Arena where
  signature := Coupling
  Law r := source_law% Econlib.Probability.IsMartingaleCoupling.convex_expect_le replacing (@IsMartingaleCoupling) with (fun μ ν π => r.readout () (μ, ν) π)
theorem source_bridge : (type_of% @Econlib.Probability.IsMartingaleCoupling.convex_expect_le) ↔ arena.Law martingaleActual := Iff.rfl
theorem actual_law : arena.Law martingaleActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.IsMartingaleCoupling.convex_expect_le
end convex_expect_le

namespace toProbDist_toMeasure
abbrev arena : Arena where
  signature := FiniteLaw
  Law r := source_law% Econlib.Probability.DiscreteLaw.toProbDist_toMeasure replacing (@DiscreteLaw.toProbDist) with (r.readout () ())
theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.toProbDist_toMeasure) ↔ arena.Law finiteLawActual := Iff.rfl
theorem actual_law : arena.Law finiteLawActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.DiscreteLaw.toProbDist_toMeasure
end toProbDist_toMeasure

namespace toProbDist_supportsOn_of_atoms_mem
abbrev arena : Arena where
  signature := FiniteLaw
  Law r := source_law% Econlib.Probability.DiscreteLaw.toProbDist_supportsOn_of_atoms_mem replacing (@DiscreteLaw.toProbDist) with (r.readout () ())
theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.toProbDist_supportsOn_of_atoms_mem) ↔ arena.Law finiteLawActual := Iff.rfl
theorem actual_law : arena.Law finiteLawActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.DiscreteLaw.toProbDist_supportsOn_of_atoms_mem
end toProbDist_supportsOn_of_atoms_mem

namespace uniform_mean
abbrev arena : Arena where
  signature := Mean
  Law r := source_law% Econlib.Probability.DiscreteLaw.uniform_mean replacing (@DiscreteLaw.mean) with (r.readout () ())
theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.uniform_mean) ↔ arena.Law meanActual := Iff.rfl
theorem actual_law : arena.Law meanActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.DiscreteLaw.uniform_mean
end uniform_mean

namespace isMartingaleCoupling
abbrev arena : Arena where
  signature := Coupling
  Law r := source_law% Econlib.Probability.BistochasticMartingaleMatrix.isMartingaleCoupling replacing (@IsMartingaleCoupling) with (fun μ ν π => r.readout () (μ, ν) π)
theorem source_bridge : (type_of% @Econlib.Probability.BistochasticMartingaleMatrix.isMartingaleCoupling) ↔ arena.Law martingaleActual := Iff.rfl
theorem actual_law : arena.Law martingaleActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.BistochasticMartingaleMatrix.isMartingaleCoupling
end isMartingaleCoupling

namespace exists_martingaleCoupling_uniform
abbrev arena : Arena where
  signature := Coupling
  Law r := source_law% Econlib.Probability.DiscreteLaw.exists_martingaleCoupling_uniform replacing (@IsMartingaleCoupling) with (fun μ ν π => r.readout () (μ, ν) π)
theorem source_bridge : (type_of% @Econlib.Probability.DiscreteLaw.exists_martingaleCoupling_uniform) ↔ arena.Law martingaleActual := Iff.rfl
theorem actual_law : arena.Law martingaleActual := by
  apply source_bridge.mp
  exact @Econlib.Probability.DiscreteLaw.exists_martingaleCoupling_uniform
end exists_martingaleCoupling_uniform
end Reg.D5.S3.Analytic.Probability.FiniteMartingaleCoupling
end

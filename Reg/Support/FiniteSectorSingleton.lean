import D5.S3.Quantum.Entanglement.FiniteSectorChannelModel

open _root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open scoped BigOperators

noncomputable section
namespace Reg.Support.FiniteSectorSingleton
universe u

/-- A normalized rank-one, one-coordinate model for the three sector countermodels. -/
abbrev model (Sector : Type u) [Fintype Sector] : Model Sector 1 where
  d := fun _ => 1
  positiveRank := by intro s; norm_num
  spectrum := fun _ _ => 1
  spectrumNonneg := by intro s j; norm_num
  spectrumSum := by intro s; simp
  spectrumAntitone := by intro s i j h; exact le_rfl

end Reg.Support.FiniteSectorSingleton

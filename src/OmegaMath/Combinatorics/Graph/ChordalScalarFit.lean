import OmegaMath.Combinatorics.Graph.EuclideanChordalScalar
import Mathlib.Tactic

/-! Omega original.

The existing scalar cycle theorem, rescaled to an arbitrary nonnegative defect. -/

namespace SimpleGraph.CirclePowerPath

variable {V : Type*} {G : SimpleGraph V}

/-- Scalar coefficient one, including defect zero, using the public cycle theorem. -/
theorem exists_scalar_fit [Finite V] (hG : G.IsChordal)
    (g : V → V → ℝ) (hrev : ∀ u v, G.Adj u v → g v u = -g u v)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj u w →
      |g u v + g v w - g u w| ≤ δ) :
    ∃ f : V → ℝ, ∀ u v, G.Adj u v → |g u v - (f v - f u)| ≤ δ := by
  have hclosed : ∀ a (p : G.Walk a a),
      0 ≤ p.scalarWeight (fun u v => g u v + δ) := by
    apply Walk.scalarWeight_nonneg_of_cycles
    · intro u v huv
      rw [hrev u v huv]
      linarith
    · intro a p hp
      rw [ScalarCycleReconstruction.scalarWeight_shift]
      have hb := EuclideanChordal.cycle_bound hG g hδ hrev htri p hp
      have hl := neg_abs_le (p.scalarWeight g)
      nlinarith
  obtain ⟨f, hf⟩ := exists_scalar_potential_of_nonneg_closed_walks
    (fun u v => g u v + δ) hclosed
  refine ⟨f, fun u v huv => abs_le.mpr ⟨?_, ?_⟩⟩
  · linarith [hf u v huv]
  · have hh := hf v u huv.symm
    rw [hrev u v huv] at hh
    linarith

end SimpleGraph.CirclePowerPath

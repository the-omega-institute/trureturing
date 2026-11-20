/- GID: D5/S3/Quantum/Dynamics/WeldedColumnEvolution
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/WeldedColumnEvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized column vectors intertwine a welded-tree walk and its weighted path. -/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap

/-! Normalized graph columns and the corresponding weighted path evolution. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.WeldedColumnEvolution

open _root_.Matrix
open scoped Matrix.Norms.Operator

private theorem exp_entry {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℂ) (v w : V) :
    NormedSpace.exp A v w = ∑' k : ℕ, (Nat.factorial k : ℚ)⁻¹ • (A ^ k) v w := by
  rw [NormedSpace.exp_eq_tsum_rat]
  let eval : Matrix V V ℂ →+ ℂ :=
    { toFun := fun M => M v w, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hContinuous : Continuous eval := continuous_apply_apply v w
  have hSum := (NormedSpace.expSeries_summable' (𝕂 := ℚ) A).hasSum.map eval hContinuous
  exact hSum.tsum_eq.symm

private theorem exp_diagonal_blocks {V Q : Type*}
    [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
    (A : Matrix V V ℂ) (B : Matrix Q Q ℂ) :
    NormedSpace.exp (fromBlocks A 0 0 B) =
      fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp B) := by
  ext (v | q) (w | r) <;>
    simp [exp_entry, fromBlocks_diagonal_pow]

private theorem exp_intertwines {V Q : Type*}
    [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
    (A : Matrix V V ℂ) (B : Matrix Q Q ℂ) (C : Matrix V Q ℂ)
    (h : A * C = C * B) :
    NormedSpace.exp A * C = C * NormedSpace.exp B := by
  let diag : Matrix (V ⊕ Q) (V ⊕ Q) ℂ := fromBlocks A 0 0 B
  let upper : Matrix (V ⊕ Q) (V ⊕ Q) ℂ := fromBlocks 0 C 0 0
  have hc : Commute diag upper := by
    change diag * upper = upper * diag
    simp [diag, upper, fromBlocks_multiply, h]
  have he := hc.exp_left.eq
  rw [show diag = fromBlocks A 0 0 B from rfl, exp_diagonal_blocks] at he
  simpa [upper, fromBlocks_multiply] using congrArg toBlocks₁₂ he

end D5.S3.Quantum.Dynamics.WeldedColumnEvolution

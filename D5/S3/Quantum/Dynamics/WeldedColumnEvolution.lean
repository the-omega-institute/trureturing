/- GID: D5/S3/Quantum/Dynamics/WeldedColumnEvolution
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/WeldedColumnEvolution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized column vectors intertwine a welded-tree walk and its weighted path. -/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.WeldedColumnEvolution

open _root_.Matrix
open scoped Matrix.Norms.L2Operator

private theorem exp_diagonal_blocks {V Q : Type*}
    [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
    (A : Matrix V V ℂ) (B : Matrix Q Q ℂ) :
    NormedSpace.exp (fromBlocks A 0 0 B) =
      fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp B) := by
  ext (v | q) (w | r) <;>
    simp [NormedSpace.exp_eq_tsum_rat, fromBlocks_diagonal_pow, Pi.tsum_apply]

private theorem exp_intertwines {V Q : Type*}
    [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]
    (A : Matrix V V ℂ) (B : Matrix Q Q ℂ) (C : Matrix V Q ℂ)
    (h : A * C = C * B) :
    NormedSpace.exp A * C = C * NormedSpace.exp B := by
  let diag : Matrix (V ⊕ Q) (V ⊕ Q) ℂ := fromBlocks A 0 0 B
  let upper : Matrix (V ⊕ Q) (V ⊕ Q) ℂ := fromBlocks 0 C 0 0
  have hc : Commute diag upper := by
    show diag * upper = upper * diag
    simp [diag, upper, fromBlocks_multiply, h]
  have he := hc.exp_left.eq
  rw [show diag = fromBlocks A 0 0 B from rfl, exp_diagonal_blocks] at he
  simpa [upper, fromBlocks_multiply] using congrArg toBlocks₁₂ he

end D5.S3.Quantum.Dynamics.WeldedColumnEvolution

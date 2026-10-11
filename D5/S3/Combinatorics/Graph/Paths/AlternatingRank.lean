/- GID: D5/S3/Combinatorics/Graph/Paths/AlternatingRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Paths/AlternatingRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: Alternating edge-subgraph ranks of paths over the binary field. -/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open scoped BigOperators
open Matrix Module

namespace D5.S3.Combinatorics.Graph.Paths.AlternatingRank

/-- The adjacency matrix of the edge subgraph selected by a Boolean edge word.
The vertices remain distinct even when a later colouring repeats a colour. -/
def adjacency : {n : ℕ} → (Fin n → Bool) → Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 2)
  | 0, _ => 0
  | n + 1, w => fun i j =>
      Fin.cases (Fin.cases 0 (fun j => if j = 0 then (if w 0 then 1 else 0) else 0) j)
        (fun i => Fin.cases (if i = 0 then (if w 0 then 1 else 0) else 0)
          (fun j => adjacency (fun k => w k.succ) i j) j) i

/-- The signed sum over all edge choices, with the sign computed in the integers. -/
noncomputable def alternatingRank (n : ℕ) : ℤ :=
  ∑ w : Fin n → Bool, (-1 : ℤ) ^ (Finset.univ.filter (fun i => w i = true)).card *
    (adjacency w).rank

end D5.S3.Combinatorics.Graph.Paths.AlternatingRank

/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Frontier
   generality: G
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors
   digest: A checked depth-first refinement rewrites a smooth fold as a frontier node sum. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Core
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-! Refining an enumeration node along its generators preserves the weighted smooth fold. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

/-- The starts `c * p ^ e`, `e < n`, visited by `powSum n`, which stops above `X`. -/
def powList : Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _ => []
  | n + 1, p, X, c => if c ≤ X then c :: powList n p X (c * p) else []

/-- One expansion of a node along its first generator; a node without generators is kept. -/
def children (X : Nat) : List Nat × Nat → List (List Nat × Nat)
  | ([], c) => [([], c)]
  | (p :: ps, c) => (powList 64 p X c).map fun c' => (ps, c')

/-- Depth-first refinement of a node, stopping at `leaf` nodes or after `k` levels. -/
def refine (X : Nat) (leaf : List Nat × Nat → Bool) :
    Nat → List Nat × Nat → List (List Nat × Nat)
  | 0, n => [n]
  | k + 1, n => if leaf n then [n] else (children X n).flatMap (refine X leaf k)

/-- `F` is the refinement of `n` whose stopping nodes are the nodes of `F`. -/
def frontierOk (X k : Nat) (n : List Nat × Nat) (F : List (List Nat × Nat)) : Bool :=
  decide (refine X (fun x => F.contains x) k n = F)

private theorem sum_powList (w : Nat → Nat) (X p : Nat) (ps : List Nat) :
    ∀ n c : Nat,
      (((powList n p X c).map fun c' => (ps, c')).map
        fun x => smoothSum w x.1 X x.2).sum =
      powSum n (fun c' => smoothSum w ps X c') p X c
  | 0, _ => rfl
  | n + 1, c => by
    change (((if c ≤ X then c :: powList n p X (c * p) else []).map
        fun c' => (ps, c')).map fun x => smoothSum w x.1 X x.2).sum =
      if c ≤ X then smoothSum w ps X c + powSum n (fun c' => smoothSum w ps X c') p X (c * p)
        else 0
    by_cases h : c ≤ X
    · rw [if_pos h, if_pos h, ← sum_powList w X p ps n (c * p)]
      rfl
    · rw [if_neg h, if_neg h]
      rfl

private theorem sum_children (w : Nat → Nat) (X : Nat) (n : List Nat × Nat) :
    ((children X n).map fun x => smoothSum w x.1 X x.2).sum = smoothSum w n.1 X n.2 := by
  obtain ⟨ps, c⟩ := n
  cases ps with
  | nil => exact Nat.add_zero _
  | cons p ps => exact sum_powList w X p ps 64 c

/-- Every depth-first refinement of a node preserves its weighted bounded smooth fold. -/
theorem sum_refine (w : Nat → Nat) (X : Nat) (leaf : List Nat × Nat → Bool) :
    ∀ (k : Nat) (n : List Nat × Nat),
      ((refine X leaf k n).map fun x => smoothSum w x.1 X x.2).sum = smoothSum w n.1 X n.2
  | 0, _ => Nat.add_zero _
  | k + 1, n => by
    change ((if leaf n then [n] else (children X n).flatMap (refine X leaf k)).map
      fun x => smoothSum w x.1 X x.2).sum = _
    by_cases h : leaf n = true
    · rw [if_pos h]
      exact Nat.add_zero _
    · rw [if_neg h]
      rw [List.flatMap_def, List.map_flatten, List.sum_flatten]
      simp only [List.map_map]
      change ((children X n).map (fun x =>
        ((refine X leaf k x).map fun y => smoothSum w y.1 X y.2).sum)).sum = _
      simp only [sum_refine w X leaf k]
      exact sum_children w X n

/-- A successful frontier check rewrites the root fold as the mapped sum over the frontier. -/
theorem smoothSum_eq_of_frontierOk (w : Nat → Nat) {X k : Nat} {n : List Nat × Nat}
    {F : List (List Nat × Nat)} (h : frontierOk X k n F = true) :
    smoothSum w n.1 X n.2 = (F.map fun x => smoothSum w x.1 X x.2).sum := by
  have hF : refine X (fun x => F.contains x) k n = F := of_decide_eq_true h
  rw [← hF]
  exact (sum_refine w X _ k n).symm

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

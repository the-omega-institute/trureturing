/- GID: D5/S3/Combinatorics/Graph/Jacobi/HairTreeShape
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/HairTreeShape
   mirror-E: none(waiver:consumed-structural-helper)
   anchors: []
   utility: none
   digest: Finite colored binary hair trees and a terminal-cherry decomposition. -/

import Mathlib.Data.Nat.Basic

/-! Structural helpers consumed by actual finite-flag grafting; no standalone
mathematical-content or first-freeze claim is made for this module. -/

namespace D5.S3.Combinatorics.Graph.Jacobi

inductive HairTree (C : Type) : Type
  | leaf : C → HairTree C
  | node : HairTree C → HairTree C → HairTree C

inductive HairContext (C : Type) : Type
  | hole : HairContext C
  | left : HairContext C → HairTree C → HairContext C
  | right : HairTree C → HairContext C → HairContext C

def HairContext.fill {C : Type} : HairContext C → HairTree C → HairTree C
  | .hole, t => t
  | .left ctx r, t => .node (ctx.fill t) r
  | .right l ctx, t => .node l (ctx.fill t)

def HairTree.leafCount {C : Type} : HairTree C → ℕ
  | .leaf _ => 1
  | .node l r => l.leafCount + r.leafCount

namespace HairTree
variable {C : Type}

/-- Every full binary tree is a leaf or has a terminal pair of leaves in an
explicit one-hole context.  The actual graph proof uses the context to retain
all exterior flags and pairings when it extracts a cherry socket. -/
theorem cherry_or_leaf (t : HairTree C) :
    (∃ c : C, t = .leaf c) ∨
      ∃ ctx : HairContext C, ∃ c d : C,
        t = ctx.fill (.node (.leaf c) (.leaf d)) := by
  induction t with
  | leaf c => exact Or.inl ⟨c, rfl⟩
  | node l r ihl ihr =>
    rcases ihl with ⟨c, hl⟩ | ⟨ctx, c, d, hl⟩
    · rcases ihr with ⟨d, hr⟩ | ⟨ctx, d, e, hr⟩
      · exact Or.inr ⟨.hole, c, d, by rw [hl, hr]; rfl⟩
      · refine Or.inr ⟨.right l ctx, d, e, ?_⟩
        exact congrArg (fun x => HairTree.node l x) hr
    · refine Or.inr ⟨.left ctx r, c, d, ?_⟩
      exact congrArg (fun x => HairTree.node x r) hl

/-- A tree with at least two leaves has an explicit terminal cherry.
This is a helper for the actual finite-flag graph extraction theorem. -/
theorem terminal_cherry_of_two_leaves (t : HairTree C)
    (ht : 2 ≤ t.leafCount) :
    ∃ ctx : HairContext C, ∃ c d : C,
      t = ctx.fill (.node (.leaf c) (.leaf d)) := by
  rcases cherry_or_leaf t with ⟨c, h⟩ | h
  · subst t
    simp [leafCount] at ht
  · exact h

end HairTree
end D5.S3.Combinatorics.Graph.Jacobi

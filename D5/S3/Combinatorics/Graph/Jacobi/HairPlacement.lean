/- GID: D5/S3/Combinatorics/Graph/Jacobi/HairPlacement
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/HairPlacement
   mirror-E: none(waiver:actual-finite-flag-graft)
   anchors: []
   utility: none
   digest: Actual terminal-cherry extraction and vanishing of binary hair-tree grafts. -/

import D5.S3.Combinatorics.Graph.Jacobi.BranchingHairTree
import D5.S3.Combinatorics.Graph.Jacobi.CherryReduction

/-! Geometric terminal-cherry extraction and vanishing of actual branching hair-tree grafts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Jacobi


/-- An actual injective flag embedding of the open tree. Its stem is paired
to a separate trivalent parent vertex. These are geometric equations, not
an assumption that any diagram-valued operation respects IHX. -/
structure HairPlacement {F : Type} (G : FlagGraph F) (t : HairTree Color) where
  flag : t.model.Flag ↪ F
  next_flag : ∀ f, G.next (flag f) = flag (t.model.next f)
  color_flag : ∀ f, G.color (flag f) = t.model.color f
  edge_nonroot : ∀ f, f ≠ t.model.root →
    G.edge (flag f) = flag (t.model.edge f)
  parent : G.Vertex
  root_pair : G.edge (flag t.model.root) = parent.flag 0
  parent_disjoint : ∀ i f, parent.flag i ≠ flag f

namespace HairPlacement

private def sumEmbedding {A B F : Type} (l : A ↪ F) (r : B ↪ F)
    (h : ∀ a b, l a ≠ r b) : A ⊕ B ↪ F where
  toFun := Sum.elim l r
  inj' := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (l.injective hab)
    · exact False.elim (h a b hab)
    · exact False.elim (h b a hab.symm)
    · exact congrArg Sum.inr (r.injective hab)

/-- Restrict an actual embedded binary vertex to its left child. -/
noncomputable def left {F : Type} {G : FlagGraph F} {l r : HairTree Color}
    (P : HairPlacement G (.node l r)) : HairPlacement G l where
  flag := ⟨fun f => P.flag (.inr (.inl f)), by
    intro a b h
    exact Sum.inl.inj (Sum.inr.inj (P.flag.injective h))⟩
  next_flag f := by
    simpa [HairTree.model, OpenHair.node] using P.next_flag (.inr (.inl f))
  color_flag f := by
    simpa [HairTree.model, OpenHair.node] using P.color_flag (.inr (.inl f))
  edge_nonroot f hf := by
    simpa [HairTree.model, OpenHair.node, OpenHair.nodeEdge, hf] using
      P.edge_nonroot (.inr (.inl f)) (by simp [HairTree.model, OpenHair.node])
  parent :=
    { flag := ⟨fun i => P.flag (.inl (finRotate 3 i)), by
        intro a b h
        exact (finRotate 3).injective (Sum.inl.inj (P.flag.injective h))⟩
      next_flag := fun i => by
        simpa [HairTree.model, OpenHair.node] using
          P.next_flag (.inl (finRotate 3 i)) }
  root_pair := by
    simpa [HairTree.model, OpenHair.node, OpenHair.nodeEdge] using
      P.edge_nonroot (.inr (.inl l.model.root)) (by simp [HairTree.model, OpenHair.node])
  parent_disjoint i f := by
    intro h
    have := P.flag.injective h
    cases this

/-- Restrict an actual embedded binary vertex to its right child. -/
noncomputable def right {F : Type} {G : FlagGraph F} {l r : HairTree Color}
    (P : HairPlacement G (.node l r)) : HairPlacement G r where
  flag := ⟨fun f => P.flag (.inr (.inr f)), by
    intro a b h
    exact Sum.inr.inj (Sum.inr.inj (P.flag.injective h))⟩
  next_flag f := by
    simpa [HairTree.model, OpenHair.node] using P.next_flag (.inr (.inr f))
  color_flag f := by
    simpa [HairTree.model, OpenHair.node] using P.color_flag (.inr (.inr f))
  edge_nonroot f hf := by
    simpa [HairTree.model, OpenHair.node, OpenHair.nodeEdge, hf] using
      P.edge_nonroot (.inr (.inr f)) (by simp [HairTree.model, OpenHair.node])
  parent :=
    { flag := ⟨fun i => P.flag (.inl (finRotate 3 (finRotate 3 i))), by
        intro a b h
        exact (finRotate 3).injective ((finRotate 3).injective
          (Sum.inl.inj (P.flag.injective h)))⟩
      next_flag := fun i => by
        simpa [HairTree.model, OpenHair.node] using
          P.next_flag (.inl (finRotate 3 (finRotate 3 i))) }
  root_pair := by
    simpa [HairTree.model, OpenHair.node, OpenHair.nodeEdge] using
      P.edge_nonroot (.inr (.inr r.model.root)) (by simp [HairTree.model, OpenHair.node])
  parent_disjoint i f := by
    intro h
    have := P.flag.injective h
    cases this

/-- Follow a shape context through actual disjoint flag embeddings. -/
noncomputable def inContext {F : Type} {G : FlagGraph F}
    (ctx : HairContext Color) (t : HairTree Color)
    (P : HairPlacement G (ctx.fill t)) : HairPlacement G t := by
  induction ctx with
  | hole => exact P
  | left ctx r ih => exact ih P.left
  | right l ctx ih => exact ih P.right

private def terminalOrder : Fin 6 ↪ (Fin 3 ⊕ Fin 3) where
  toFun := ![.inl 0, .inr 0, .inl 1, .inr 1, .inr 2, .inl 2]
  inj' := by decide

/-- The terminal binary node and its actual trivalent parent are exactly
one X resolution. All flags outside this eight-flag region are untouched. -/
noncomputable def terminalCherry {F : Type} {G : FlagGraph F} {c d : Color}
    (P : HairPlacement G (.node (.leaf c) (.leaf d))) : G.Cherry := by
  let treeVertex : Fin 3 ↪ F :=
    ⟨fun i => P.flag (.inl i), by intro a b h; exact Sum.inl.inj (P.flag.injective h)⟩
  let combined : Fin 3 ⊕ Fin 3 ↪ F :=
    sumEmbedding treeVertex P.parent.flag (by
      intro i j h
      exact P.parent_disjoint j (.inl i) h.symm)
  let socketFlag : Fin 6 ↪ F := terminalOrder.trans combined
  refine
    { socket :=
        { flag := socketFlag
          next_flag := ?_
          central := ?_ }
      leftLeaf := P.flag (.inr (.inl ()))
      rightLeaf := P.flag (.inr (.inr ()))
      leaf_ne := ?_
      left_pair := ?_
      right_pair := ?_
      left_fixed := ?_
      right_fixed := ?_
      left_ordinary := ?_
      right_ordinary := ?_ }
  · intro i
    fin_cases i
    · simpa [socketFlag, terminalOrder, combined, sumEmbedding, treeVertex,
        FlagGraph.socketX, HairTree.model, OpenHair.node] using P.next_flag (.inl 0)
    · change G.next (P.parent.flag 0) = P.parent.flag 1
      exact P.parent.next_flag 0
    · simpa [socketFlag, terminalOrder, combined, sumEmbedding, treeVertex,
        FlagGraph.socketX, HairTree.model, OpenHair.node] using P.next_flag (.inl 1)
    · change G.next (P.parent.flag 1) = P.parent.flag 2
      exact P.parent.next_flag 1
    · change G.next (P.parent.flag 2) = P.parent.flag 0
      exact P.parent.next_flag 2
    · simpa [socketFlag, terminalOrder, combined, sumEmbedding, treeVertex,
        FlagGraph.socketX, HairTree.model, OpenHair.node] using P.next_flag (.inl 2)
  · simpa [socketFlag, terminalOrder, combined, sumEmbedding, treeVertex,
      HairTree.model, OpenHair.node] using P.root_pair
  · intro h
    have := P.flag.injective h
    cases this
  · simpa [socketFlag, terminalOrder, combined, sumEmbedding, treeVertex,
      HairTree.model, OpenHair.node, OpenHair.nodeEdge, OpenHair.leaf] using
      P.edge_nonroot (.inl 1) (by simp [HairTree.model, OpenHair.node])
  · simpa [socketFlag, terminalOrder, combined, sumEmbedding, treeVertex,
      HairTree.model, OpenHair.node, OpenHair.nodeEdge, OpenHair.leaf] using
      P.edge_nonroot (.inl 2) (by simp [HairTree.model, OpenHair.node])
  · simpa [HairTree.model, OpenHair.node, OpenHair.leaf] using
      P.next_flag (.inr (.inl ()))
  · simpa [HairTree.model, OpenHair.node, OpenHair.leaf] using
      P.next_flag (.inr (.inr ()))
  · exact ⟨c, P.color_flag (.inr (.inl ()))⟩
  · exact ⟨d, P.color_flag (.inr (.inr ()))⟩

/-- Actual terminal-cherry extraction. The shape theorem is consumed by
following its context through the geometric flag embedding, not just imported. -/
theorem extractCherry {F : Type} {G : FlagGraph F}
    (t : HairTree Color) (ht : 2 ≤ t.leafCount) (P : HairPlacement G t) : Nonempty G.Cherry := by
  obtain ⟨ctx, c, d, he⟩ := t.terminal_cherry_of_two_leaves ht
  subst t
  exact ⟨(inContext ctx _ P).terminalCherry⟩

end HairPlacement

/-- The entire tree in an actual subdividing graft has the required embedding;
its external parent is the new trivalent subdivision, even for a two-leaf tree. -/
noncomputable def graftPlacement {F : Type} (G : FlagGraph F) (a : F)
    (t : HairTree Color) : HairPlacement (G.graft a t.model) t where
  flag := ⟨fun f => .inr (.inr f), by intro x y h; exact Sum.inr.inj (Sum.inr.inj h)⟩
  next_flag _ := rfl
  color_flag _ := rfl
  edge_nonroot f hf := by
    change FlagGraph.graftEdge G a t.model (.inr (.inr f)) =
      .inr (.inr (t.model.edge f))
    simp [FlagGraph.graftEdge, hf]
  parent :=
    { flag := ⟨fun i => .inr (.inl i), by intro x y h; exact Sum.inl.inj (Sum.inr.inj h)⟩
      next_flag := fun _ => rfl }
  root_pair := by
    change FlagGraph.graftEdge G a t.model (.inr (.inr t.model.root)) = .inr (.inl 0)
    simp [FlagGraph.graftEdge]
  parent_disjoint i f := by
    change (Sum.inr (Sum.inl i) : FlagGraph.GraftFlag (F := F) t.model) ≠
      Sum.inr (Sum.inr f)
    simp

/-- Every actual graft with at least two colored leaves is zero in the true
AS/IHX/ordinary-CL graph quotient, allowing arbitrary numbered exterior anchors.
No abstract IHX compatibility is assumed. -/
theorem branching_hair_tree_vanishes {F : Type} [Finite F]
    (G : FlagGraph F) (a : F) (t : HairTree Color) (ht : 2 ≤ t.leafCount) :
    classOf (G.graft a t.model) = 0 := by
  obtain ⟨C⟩ := HairPlacement.extractCherry t ht (graftPlacement G a t)
  exact cherry_zero _ C

end D5.S3.Combinatorics.Graph.Jacobi

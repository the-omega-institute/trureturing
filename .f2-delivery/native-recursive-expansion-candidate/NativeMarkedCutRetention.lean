/- UNCOMPILED actual b-edge preservation for the recursive marked state.
   Every deleted supplier b edge has the supplier terminal. New marked
   b edges have another, remaining terminal, so no supplier cut can remove
   them. Actual child and parent joining retain these actual edges. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveCycleStep
import D5.S3.Combinatorics.Graph.Walks.ActualRetainedEdges

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualRetainedEdges
open private anchor_coordinates bc_terminal from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open private parentPiece childLift from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly
open private finish_eq_last from
  D5.S3.Combinatorics.Graph.Walks.ActualCyclePieceReordering

private theorem right_port_terminal {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (i : ℕ) : rightPort F i (Fin.last m) = F.terminal := by
  rw [rightPort, bc_terminal (by omega : 2 ≤ m), (anchor_coordinates F).2]

/-- Terminal labels distinguish actual undirected b edges, not only
their chosen orientation: both endpoints of a b edge have the same last label. -/
theorem native_b_edges_distinct_terminals {m : ℕ} (x y : Configuration m)
    (hxy : x (Fin.last m) ≠ y (Fin.last m)) : s(x, x * b m) ≠ s(y, y * b m) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨hx, _⟩ | ⟨hx, _⟩
  · exact hxy (congrArg (fun z => z (Fin.last m)) hx)
  · have ht := congrArg (fun z => z (Fin.last m)) hx
    simp only [Equiv.Perm.mul_apply, b_last] at ht
    exact hxy ht

/-- A genuine b edge with a different remaining terminal is not any of
the special supplier cuts. The conclusion is about the actual subtype edge. -/
theorem native_remaining_b_not_special_cut {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (x y : {z : Configuration m // SpecialDomain F hB z})
    (hy : y.val = x.val * b m) (hx : x.val (Fin.last m) ≠ F.terminal) :
    s(x, y) ∉ specialCuts hm F hB := by
  classical
  intro he
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
  have h := congrArg (Sym2.map Subtype.val) hi
  change s(rightPort F i.val, leftPort F i.val) = s(x.val, y.val) at h
  rw [hy, leftPort] at h
  exact native_b_edges_distinct_terminals x.val (rightPort F i.val)
    (by rw [right_port_terminal hm F i.val]; exact hx) h.symm

/-- Exact actual uncut-piece inventory and joining are enough to preserve
every old remaining-terminal b edge in the special full path. -/
theorem native_special_path_keeps_remaining_b {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    {a : {z : Configuration m // SpecialDomain F hB z}}
    (w : (domainGraph (SpecialDomain F hB)).Walk a a)
    (p : Piece (domainGraph (SpecialDomain F hB)))
    (ps : List (Piece (domainGraph (SpecialDomain F hB))))
    (hinv : ∀ e, e ∈ ((p :: ps).flatMap fun z => z.walk.edges) ↔
      e ∈ w.edgeSet ∧ e ∉ specialCuts hm F hB)
    {u v : {z : Configuration m // SpecialDomain F hB z}}
    (q : (domainGraph (SpecialDomain F hB)).Walk u v)
    (hedges : q.edges = chainEdges p ps)
    (x y : {z : Configuration m // SpecialDomain F hB z})
    (hy : y.val = x.val * b m) (hx : x.val (Fin.last m) ≠ F.terminal)
    (he : s(x, y) ∈ w.edgeSet) : s(x, y) ∈ q.edges := by
  have hpieces := (hinv s(x, y)).mpr
    ⟨he, native_remaining_b_not_special_cut hm F hB x y hy hx⟩
  obtain ⟨z, hz, hez⟩ := List.mem_flatMap.mp hpieces
  rw [hedges]
  exact actual_chain_keeps_piece_edges p ps z hz s(x, y) hez

/-- Ordinary child opening removes only its actual supplier b edge.
Different remaining terminals distinguish every next marked b edge from it. -/
theorem native_other_path_keeps_remaining_b {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (j : Fin F.base.length) (hj : 0 < j.val)
    {a : {z : Configuration m // ChildDomain (childGap F j) z}}
    (w : (domainGraph (ChildDomain (childGap F j))).Walk a a)
    (q : ActualChildPath F j)
    (hinv : ∀ e, e ∈ q.piece.walk.edges ↔ e ∈ w.edges ∧
      e ≠ s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj))
    (x y : {z : Configuration m // ChildDomain (childGap F j) z})
    (hy : y.val = x.val * b m) (hx : x.val (Fin.last m) ≠ F.terminal)
    (he : s(x, y) ∈ w.edges) : s(x, y) ∈ q.piece.walk.edges := by
  apply (hinv s(x, y)).mpr
  refine ⟨he, ?_⟩
  intro h
  have hv := congrArg (Sym2.map Subtype.val) h
  change s(x.val, y.val) = s(rightPort F (k + j.val), leftPort F (k + j.val)) at hv
  rw [hy, leftPort] at hv
  exact native_b_edges_distinct_terminals x.val (rightPort F (k + j.val))
    (by rw [right_port_terminal hm F]; exact hx) hv

/-- The actual outer cycle retains every actual edge of every lifted
child path, expressed again in the original native configuration type.
The child association and literal inventory are those returned by the
strengthened native parent constructor. -/
theorem native_parent_cycle_keeps_child_path_edges {m k : ℕ}
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (paths : ∀ j : Fin F.base.length, ActualChildPath F j)
    (pieces : Fin F.base.length → Piece (domainGraph (ParentDomain F)))
    (hpieces : ∀ j, pieces j = parentPiece F j (paths j))
    {base : {x : Configuration m // ParentDomain F x}}
    (c : (domainGraph (ParentDomain F)).Walk base base)
    (hedges : c.edges = s(base, (pieces ⟨F.base.length - 1, by omega⟩).finish) ::
      (chainEdges (pieces ⟨0, by omega⟩)
        (List.ofFn fun i : Fin (F.base.length - 1) =>
          pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩)).reverse)
    (j : Fin F.base.length)
    (x y : {z : Configuration m // ChildDomain (childGap F j) z})
    (he : s(x, y) ∈ (paths j).piece.walk.edges) :
    s(x.val, y.val) ∈ c.edges.map (Sym2.map Subtype.val) := by
  let p := pieces ⟨0, by omega⟩
  let ps := List.ofFn fun i : Fin (F.base.length - 1) =>
    pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩
  have hlist : p :: ps = List.ofFn pieces := by
    apply List.ext_getElem
    · simp only [List.length_cons, List.length_ofFn]; omega
    · intro i hi hj
      cases i with
      | zero => simp only [List.getElem_cons_zero, List.getElem_ofFn]; rfl
      | succ i => simp only [List.getElem_cons_succ, List.getElem_ofFn]; rfl
  have hfinish : finish p ps = (pieces ⟨F.base.length - 1, by omega⟩).finish := by
    rw [finish_eq_last, hlist, List.getLast_ofFn]
  have hclose : c.edges = s(base, finish p ps) :: (chainEdges p ps).reverse := by
    simpa only [hfinish, p, ps] using hedges
  have hemap : s(childLift F j x, childLift F j y) ∈ (pieces j).walk.edges := by
    rw [hpieces j]
    change _ ∈ ((paths j).piece.walk.map (childLift F j)).edges
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x, y), he, rfl⟩
  have hz : pieces j ∈ p :: ps := by rw [hlist]; exact List.mem_ofFn.mpr ⟨j, rfl⟩
  have hec := actual_closed_route_keeps_piece_edges p ps c hclose
    (pieces j) hz s(childLift F j x, childLift F j y) hemap
  exact List.mem_map.mpr ⟨s(childLift F j x, childLift F j y), hec, rfl⟩

#print axioms native_b_edges_distinct_terminals
#print axioms native_remaining_b_not_special_cut
#print axioms native_special_path_keeps_remaining_b
#print axioms native_other_path_keeps_remaining_b
#print axioms native_parent_cycle_keeps_child_path_edges

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion

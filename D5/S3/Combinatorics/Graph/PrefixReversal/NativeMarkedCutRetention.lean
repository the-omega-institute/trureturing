/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Preserve Protected a and Remaining b Edges Through Native Recursion. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveCycleStep
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
import D5.S3.Combinatorics.Graph.Walks.ActualRetainedEdges

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
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
open private layer_a layer_b from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates

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
    dsimp only [p, ps]
    apply List.ext_getElem
    · simp only [List.length_cons, List.length_ofFn]; omega
    · intro i hi hj
      cases i with
      | zero => simp only [List.getElem_cons_zero, List.getElem_ofFn]
      | succ i => simp only [List.getElem_cons_succ, List.getElem_ofFn]
  have hfinish : finish p ps = (pieces ⟨F.base.length - 1, by omega⟩).finish := by
    have hn : List.ofFn pieces ≠ [] := by
      intro hn
      have hlen := congrArg List.length hn
      simp only [List.length_ofFn, List.length_nil] at hlen
      omega
    calc
      finish p ps = ((p :: ps).getLast (by simp)).finish := finish_eq_last p ps
      _ = ((List.ofFn pieces).getLast hn).finish :=
        congrArg Piece.finish (List.getLast_congr (by simp) hn hlist)
      _ = _ := by rw [List.getLast_ofFn]
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

/-- The independently defined child partition transfers the genuine
remaining-label b invariant from actual retained child paths to the same
actual parent cycle. Each b step stays in its unique child deletion layer.
The new selected terminal is excluded by the parent residual-label guard. -/
theorem native_parent_cycle_keeps_remaining_b {m k : ℕ}
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (paths : ∀ j : Fin F.base.length, ActualChildPath F j)
    (hchild : ∀ (j : Fin F.base.length)
      (x y : {z : Configuration m // ChildDomain (childGap F j) z}),
      y.val = x.val * b m → x.val (Fin.last m) ∉ F.selected.toFinset →
        x.val (Fin.last m) ≠ F.terminal → s(x, y) ∈ (paths j).piece.walk.edges)
    (pieces : Fin F.base.length → Piece (domainGraph (ParentDomain F)))
    (hpieces : ∀ j, pieces j = parentPiece F j (paths j))
    {base : {z : Configuration m // ParentDomain F z}}
    (c : (domainGraph (ParentDomain F)).Walk base base)
    (hedges : c.edges = s(base, (pieces ⟨F.base.length - 1, by omega⟩).finish) ::
      (chainEdges (pieces ⟨0, by omega⟩)
        (List.ofFn fun i : Fin (F.base.length - 1) =>
          pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩)).reverse)
    (x y : {z : Configuration m // ParentDomain F z})
    (hy : y.val = x.val * b m)
    (hx : x.val (Fin.last m) ∉ insert F.terminal F.selected.toFinset) :
    s(x.val, y.val) ∈ c.edges.map (Sym2.map Subtype.val) := by
  classical
  obtain ⟨j, hj, _⟩ := (native_child_gap_partition F hB x.val).mp x.property
  have hychild : ChildDomain (childGap F j) y.val := by
    rw [hy]
    exact layer_b _ _ hj
  let x' : {z : Configuration m // ChildDomain (childGap F j) z} := ⟨x.val, hj⟩
  let y' : {z : Configuration m // ChildDomain (childGap F j) z} := ⟨y.val, hychild⟩
  have hguards : x.val (Fin.last m) ≠ F.terminal ∧
      x.val (Fin.last m) ∉ F.selected.toFinset := by
    simpa only [Finset.mem_insert, not_or] using hx
  have he : s(x', y') ∈ (paths j).piece.walk.edges :=
    hchild j x' y' hy hguards.2 hguards.1
  exact native_parent_cycle_keeps_child_path_edges F hB paths pieces hpieces c hedges
    j x' y' he

/-- Full reversal changes the terminal label of every actual tuple with
at least two positions. This distinguishes an a edge from a b supplier cut. -/
theorem native_a_changes_terminal {m : ℕ} (hm : 3 ≤ m) (x : Configuration m) :
    (x * a m) (Fin.last m) ≠ x (Fin.last m) := by
  intro he
  have hi : (0 : Fin (m + 1)) = Fin.last m := x.injective (by
    simpa only [Equiv.Perm.mul_apply, a_apply, Fin.rev_last] using he)
  have hv := congrArg Fin.val hi
  simp only [Fin.val_zero, Fin.val_last] at hv
  omega

/-- The statement is about undirected edges. Both endpoints of b have
the same terminal; the two endpoints of a have different terminals. -/
theorem native_a_edge_ne_b_edge {m : ℕ} (hm : 3 ≤ m)
    (x y : Configuration m) : s(x, x * a m) ≠ s(y, y * b m) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hxl := congrArg (fun z => z (Fin.last m)) hx
    have hyl := congrArg (fun z => z (Fin.last m)) hy
    simp only [Equiv.Perm.mul_apply, b_last] at hyl
    exact native_a_changes_terminal hm x (hyl.trans hxl.symm)
  · have hxl := congrArg (fun z => z (Fin.last m)) hx
    have hyl := congrArg (fun z => z (Fin.last m)) hy
    simp only [Equiv.Perm.mul_apply, b_last] at hxl
    exact native_a_changes_terminal hm x (hyl.trans hxl.symm)

/-- No actual a edge is a supplier b cut, independently of which protected
terminal-label pair is used by the previous cycle's a invariant. -/
theorem native_a_not_special_cut {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (x y : {z : Configuration m // SpecialDomain F hB z})
    (hy : y.val = x.val * a m) : s(x, y) ∉ specialCuts hm F hB := by
  classical
  intro he
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
  have h := congrArg (Sym2.map Subtype.val) hi
  change s(rightPort F i.val, leftPort F i.val) = s(x.val, y.val) at h
  rw [hy, leftPort] at h
  exact native_a_edge_ne_b_edge hm x.val (rightPort F i.val) h.symm

/-- Special joining retains every actual previous a edge: only b edges
are opened, and literal chain inventory retains all remaining piece edges. -/
theorem native_special_path_keeps_a {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    {base : {z : Configuration m // SpecialDomain F hB z}}
    (w : (domainGraph (SpecialDomain F hB)).Walk base base)
    (p : Piece (domainGraph (SpecialDomain F hB)))
    (ps : List (Piece (domainGraph (SpecialDomain F hB))))
    (hinv : ∀ e, e ∈ ((p :: ps).flatMap fun z => z.walk.edges) ↔
      e ∈ w.edgeSet ∧ e ∉ specialCuts hm F hB)
    {u v : {z : Configuration m // SpecialDomain F hB z}}
    (q : (domainGraph (SpecialDomain F hB)).Walk u v)
    (hedges : q.edges = chainEdges p ps)
    (x y : {z : Configuration m // SpecialDomain F hB z})
    (hy : y.val = x.val * a m) (he : s(x, y) ∈ w.edgeSet) :
    s(x, y) ∈ q.edges := by
  have hpieces := (hinv s(x, y)).mpr
    ⟨he, native_a_not_special_cut hm F hB x y hy⟩
  obtain ⟨z, hz, hez⟩ := List.mem_flatMap.mp hpieces
  rw [hedges]
  exact actual_chain_keeps_piece_edges p ps z hz s(x, y) hez

/-- An ordinary opening also removes only its actual supplier b edge,
so every previous a edge remains in the selected actual complement path. -/
theorem native_other_path_keeps_a {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (j : Fin F.base.length) (hj : 0 < j.val)
    {base : {z : Configuration m // ChildDomain (childGap F j) z}}
    (w : (domainGraph (ChildDomain (childGap F j))).Walk base base)
    (q : ActualChildPath F j)
    (hinv : ∀ e, e ∈ q.piece.walk.edges ↔ e ∈ w.edges ∧
      e ≠ s(ordinaryRight hm F hB j hj, ordinaryLeft hm F hB j hj))
    (x y : {z : Configuration m // ChildDomain (childGap F j) z})
    (hy : y.val = x.val * a m) (he : s(x, y) ∈ w.edges) :
    s(x, y) ∈ q.piece.walk.edges := by
  apply (hinv s(x, y)).mpr
  refine ⟨he, ?_⟩
  intro h
  have hv := congrArg (Sym2.map Subtype.val) h
  change s(x.val, y.val) = s(rightPort F (k + j.val), leftPort F (k + j.val)) at hv
  rw [hy, leftPort] at hv
  exact native_a_edge_ne_b_edge hm x.val (rightPort F (k + j.val)) hv

/-- The exact protected-a invariant is inherited on the same actual
parent cycle. The guard excludes only the fixed p/q terminal-label pair;
it does not assert that previous missing a edges have been restored. -/
theorem native_parent_cycle_keeps_protected_a {m k : ℕ}
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (p q : Fin (m + 1))
    (paths : ∀ j : Fin F.base.length, ActualChildPath F j)
    (hchild : ∀ (j : Fin F.base.length)
      (x y : {z : Configuration m // ChildDomain (childGap F j) z}),
      y.val = x.val * a m → s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q) →
        s(x, y) ∈ (paths j).piece.walk.edges)
    (pieces : Fin F.base.length → Piece (domainGraph (ParentDomain F)))
    (hpieces : ∀ j, pieces j = parentPiece F j (paths j))
    {base : {z : Configuration m // ParentDomain F z}}
    (c : (domainGraph (ParentDomain F)).Walk base base)
    (hedges : c.edges = s(base, (pieces ⟨F.base.length - 1, by omega⟩).finish) ::
      (chainEdges (pieces ⟨0, by omega⟩)
        (List.ofFn fun i : Fin (F.base.length - 1) =>
          pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩)).reverse)
    (x y : {z : Configuration m // ParentDomain F z})
    (hy : y.val = x.val * a m)
    (hx : s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(p, q)) :
    s(x.val, y.val) ∈ c.edges.map (Sym2.map Subtype.val) := by
  classical
  obtain ⟨j, hj, _⟩ := (native_child_gap_partition F hB x.val).mp x.property
  have hychild : ChildDomain (childGap F j) y.val := by
    rw [hy]
    exact layer_a _ _ hj
  let x' : {z : Configuration m // ChildDomain (childGap F j) z} := ⟨x.val, hj⟩
  let y' : {z : Configuration m // ChildDomain (childGap F j) z} := ⟨y.val, hychild⟩
  have he : s(x', y') ∈ (paths j).piece.walk.edges := hchild j x' y' hy hx
  exact native_parent_cycle_keeps_child_path_edges F hB paths pieces hpieces c hedges
    j x' y' he

#print axioms native_b_edges_distinct_terminals
#print axioms native_remaining_b_not_special_cut
#print axioms native_special_path_keeps_remaining_b
#print axioms native_other_path_keeps_remaining_b
#print axioms native_parent_cycle_keeps_child_path_edges
#print axioms native_parent_cycle_keeps_remaining_b
#print axioms native_a_changes_terminal
#print axioms native_a_edge_ne_b_edge
#print axioms native_a_not_special_cut
#print axioms native_special_path_keeps_a
#print axioms native_other_path_keeps_a
#print axioms native_parent_cycle_keeps_protected_a

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion

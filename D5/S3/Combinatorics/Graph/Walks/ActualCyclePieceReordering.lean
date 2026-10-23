/- GID: D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supplied actual cycle pieces are oriented along a route and joined with exact support and retained-edge inventories. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
import D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualCyclePieceReordering

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open private join join_support join_edges from
  D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Fix the actual slicing selected from the actual cycle theorem. The later
endpoint law is about these pieces, rather than an abstract realization. -/
noncomputable def cyclePieces (E : Finset (Sym2 V)) {a : V}
    (w : G.Walk a a) (hw : w.IsHamiltonianCycle) (hE : E.Nonempty)
    (hcuts : ∀ e ∈ E, e ∈ w.edgeSet) : List (Piece G) := by
  letI : Finite V := hw.finite
  letI : Fintype V := Fintype.ofFinite V
  exact Classical.choose (exists_cycle_edge_slicing E w hw hE hcuts)

private theorem cyclePieces_spec (E : Finset (Sym2 V)) {a : V}
    (w : G.Walk a a) (hw : w.IsHamiltonianCycle) (hE : E.Nonempty)
    (hcuts : ∀ e ∈ E, e ∈ w.edgeSet) :
    (∀ z ∈ cyclePieces E w hw hE hcuts, z.walk.IsPath) ∧
    (∀ v, ((cyclePieces E w hw hE hcuts).flatMap fun z => z.walk.support).count v = 1) ∧
    (∀ e, e ∈ ((cyclePieces E w hw hE hcuts).flatMap fun z => z.walk.edges) ↔
      e ∈ w.edgeSet ∧ e ∉ E) ∧
    (cyclePieces E w hw hE hcuts).length = E.card := by
  letI : Finite V := hw.finite
  letI : Fintype V := Fintype.ofFinite V
  exact Classical.choose_spec (exists_cycle_edge_slicing E w hw hE hcuts)

def routeEdge {n : ℕ} (route : Fin (2 * n) → V) (i : Fin n) : Sym2 V :=
  s(route ⟨2 * i.val, by have hi := i.isLt; omega⟩,
    route ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)

private theorem orient_piece (p : Piece G) (x y : V)
    (he : s(p.start, p.finish) = s(x, y)) :
    ∃ q : Piece G, q.start = x ∧ q.finish = y ∧
      q.walk.support.Perm p.walk.support ∧ q.walk.edges.Perm p.walk.edges := by
  rcases Sym2.eq_iff.mp he with ⟨hs, hf⟩ | ⟨hs, hf⟩
  · exact ⟨⟨x, y, p.walk.copy hs hf⟩, rfl, rfl,
      by simp only [SimpleGraph.Walk.support_copy]; exact List.Perm.refl _,
      by simp only [SimpleGraph.Walk.edges_copy]; exact List.Perm.refl _⟩
  · exact ⟨⟨x, y, p.walk.reverse.copy hf hs⟩, rfl, rfl,
      by simp only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse]
         exact List.reverse_perm _,
      by simp only [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse]
         exact List.reverse_perm _⟩

private theorem flatMap_perm_of_pointwise {α β : Type*} (l : List α)
    (f g : α → List β) (h : ∀ x ∈ l, (f x).Perm (g x)) :
    (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    exact (h x List.mem_cons_self).append
      (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- Exact support and filtered-edge inventories of a supplied Hamilton
cycle earn the number of supplied pieces. Each piece contributes one more
support vertex than edge, including an actual nil piece at adjacent cuts. -/
theorem actual_cycle_partition_inventory (E : Finset (Sym2 V)) {a : V}
    (w : G.Walk a a) (hw : w.IsHamiltonianCycle) (pieces : List (Piece G))
    (hs : (pieces.flatMap fun z => z.walk.support).Perm w.support.tail)
    (he : (pieces.flatMap fun z => z.walk.edges).Perm
      (w.edges.filter fun e => decide (e ∉ E)))
    (hcuts : ∀ e ∈ E, e ∈ w.edges) :
    (∀ v, (pieces.flatMap fun z => z.walk.support).count v = 1) ∧
    (∀ e, e ∈ pieces.flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edgeSet ∧ e ∉ E) ∧ pieces.length = E.card := by
  classical
  have hcount (v : V) : (pieces.flatMap fun z => z.walk.support).count v = 1 := by
    rw [hs.count_eq v]
    exact (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mp hw).2 v
  have hedge (e : Sym2 V) : e ∈ pieces.flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edgeSet ∧ e ∉ E := by
    rw [he.mem_iff]
    simp only [List.mem_filter, decide_eq_true_eq, SimpleGraph.Walk.mem_edgeSet]
  have pieceLength (ps : List (Piece G)) :
      (ps.flatMap fun z => z.walk.support).length =
        (ps.flatMap fun z => z.walk.edges).length + ps.length := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_edges] at ih ⊢
      omega
  have hsubset : E ⊆ w.edges.toFinset := by
    intro e he
    exact List.mem_toFinset.mpr (hcuts e he)
  have hn := hw.isCycle.isTrail.edges_nodup
  have hwhole : w.edges.toFinset.card = w.length :=
    (List.toFinset_card_of_nodup hn).trans (SimpleGraph.Walk.length_edges w)
  have hset : (w.edges.filter fun e => decide (e ∉ E)).toFinset = w.edges.toFinset \ E := by
    ext e
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_sdiff]
  have hf := List.toFinset_card_of_nodup (hn.filter (fun e => decide (e ∉ E)))
  rw [hset, Finset.card_sdiff_of_subset hsubset, hwhole] at hf
  have hc : E.card ≤ w.length := by
    simpa only [hwhole] using Finset.card_le_card hsubset
  have hsl := hs.length_eq
  have hel := he.length_eq
  have hlength := pieceLength pieces
  simp only [List.length_tail, SimpleGraph.Walk.length_support] at hsl
  exact ⟨hcount, hedge, by omega⟩

/-- Every supplied actual piece is assigned one whole route edge by the earned
endpoint law. Distinct actual slices cannot receive the same route edge:
that would repeat an endpoint in the exact sliced support partition.
Finite cardinality then makes this assignment a permutation. -/
theorem actual_partition_pieces_reordered (E : Finset (Sym2 V)) {a : V}
    (w : G.Walk a a) (pieces : List (Piece G)) (n : ℕ)
    (hcount : ∀ v, (pieces.flatMap fun z => z.walk.support).count v = 1)
    (hedges : ∀ e, e ∈ pieces.flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edgeSet ∧ e ∉ E) (hlen : pieces.length = n)
    (route : Fin (2 * n) → V)
    (hmatch : ∀ z ∈ pieces,
      ∃ i : Fin n, s(z.start, z.finish) = routeEdge route i) :
    ∃ ordered : Fin n → Piece G,
      (∀ i, (ordered i).start = route ⟨2 * i.val, by have hi := i.isLt; omega⟩ ∧
        (ordered i).finish = route ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩) ∧
      (∀ v, ((List.ofFn ordered).flatMap fun z => z.walk.support).count v = 1) ∧
      (∀ e, e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
        e ∈ w.edgeSet ∧ e ∉ E) := by
  classical
  let old : Fin n → Piece G := fun i => pieces.get (Fin.cast hlen.symm i)
  have hmem (i : Fin n) : old i ∈ pieces := List.get_mem _ _
  have hold : List.ofFn old = pieces := by
    rw [List.ofFn_congr hlen.symm old]
    simpa only [old, Fin.cast_cast, Fin.cast_refl, id_eq] using List.ofFn_get pieces
  let index (i : Fin n) : Fin n := Classical.choose (hmatch (old i) (hmem i))
  have hindex (i : Fin n) :
      s((old i).start, (old i).finish) = routeEdge route (index i) :=
    Classical.choose_spec (hmatch (old i) (hmem i))
  have hn : (pieces.flatMap fun z => z.walk.support).Nodup :=
    List.nodup_iff_count_le_one.mpr (fun v => by rw [hcount v])
  have hd := (List.nodup_flatMap.mp hn).2
  have hinj : Function.Injective index := by
    intro i j hij
    have he : s((old i).start, (old i).finish) = s((old j).start, (old j).finish) :=
      (hindex i).trans ((congrArg (routeEdge route) hij).trans (hindex j).symm)
    have hx : (old i).start ∈ (old j).walk.support := by
      rcases Sym2.eq_iff.mp he with ⟨hs, _⟩ | ⟨hs, _⟩
      · rw [hs]; exact (old j).walk.start_mem_support
      · rw [hs]; exact (old j).walk.end_mem_support
    by_contra hne
    have hvals : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hvals with hlt | hgt
    · have hdis : List.Disjoint (old i).walk.support (old j).walk.support :=
        hd.rel_get_of_lt (by simpa only [Fin.lt_def, Fin.val_cast] using hlt)
      exact List.disjoint_left.mp hdis (old i).walk.start_mem_support hx
    · have hdis : List.Disjoint (old j).walk.support (old i).walk.support :=
        hd.rel_get_of_lt (by simpa only [Fin.lt_def, Fin.val_cast] using hgt)
      exact List.disjoint_left.mp hdis hx (old i).walk.start_mem_support
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective index
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  let raw (i : Fin n) := old (σ.symm i)
  have hraw (i : Fin n) :
      s((raw i).start, (raw i).finish) = routeEdge route i := by
    simpa only [raw, show index (σ.symm i) = i from σ.apply_symm_apply i] using
      hindex (σ.symm i)
  have hex (i : Fin n) := orient_piece (raw i)
    (route ⟨2 * i.val, by have hi := i.isLt; omega⟩)
    (route ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩) (hraw i)
  let ordered (i : Fin n) : Piece G := Classical.choose (hex i)
  have hspec (i : Fin n) := Classical.choose_spec (hex i)
  have hrawperm : (List.ofFn raw).Perm pieces := by
    simpa only [raw, Function.comp_def, hold] using Equiv.Perm.ofFn_comp_perm σ.symm old
  have hsperm : ((List.ofFn ordered).flatMap fun z => z.walk.support).Perm
      (pieces.flatMap fun z => z.walk.support) := by
    have hpoint : ((List.ofFn ordered).flatMap fun z => z.walk.support).Perm
        ((List.ofFn raw).flatMap fun z => z.walk.support) := by
      rw [List.ofFn_eq_map, List.ofFn_eq_map, List.flatMap_map, List.flatMap_map]
      exact flatMap_perm_of_pointwise (List.finRange n)
        (fun i => (ordered i).walk.support) (fun i => (raw i).walk.support)
        (fun i _ => (hspec i).2.2.1)
    exact hpoint.trans (hrawperm.flatMap_right (fun z => z.walk.support))
  have heperm : ((List.ofFn ordered).flatMap fun z => z.walk.edges).Perm
      (pieces.flatMap fun z => z.walk.edges) := by
    have hpoint : ((List.ofFn ordered).flatMap fun z => z.walk.edges).Perm
        ((List.ofFn raw).flatMap fun z => z.walk.edges) := by
      rw [List.ofFn_eq_map, List.ofFn_eq_map, List.flatMap_map, List.flatMap_map]
      exact flatMap_perm_of_pointwise (List.finRange n)
        (fun i => (ordered i).walk.edges) (fun i => (raw i).walk.edges)
        (fun i _ => (hspec i).2.2.2)
    exact hpoint.trans (hrawperm.flatMap_right (fun z => z.walk.edges))
  refine ⟨ordered, fun i => ⟨(hspec i).1, (hspec i).2.1⟩, ?_, ?_⟩
  · intro v
    exact (hsperm.count_eq v).trans (hcount v)
  · intro e
    exact heperm.mem_iff.trans (hedges e)

/-- Every actual slice is assigned one whole route edge by the earned
endpoint law. Distinct actual slices cannot receive the same route edge:
that would repeat an endpoint in the exact sliced support partition.
Finite cardinality then makes this assignment a permutation. -/
theorem actual_cycle_slices_reordered (E : Finset (Sym2 V)) {a : V}
    (w : G.Walk a a) (hw : w.IsHamiltonianCycle) (hE : E.Nonempty)
    (hcuts : ∀ e ∈ E, e ∈ w.edgeSet) (n : ℕ) (hcard : E.card = n)
    (route : Fin (2 * n) → V)
    (hmatch : ∀ z ∈ cyclePieces E w hw hE hcuts,
      ∃ i : Fin n, s(z.start, z.finish) = routeEdge route i) :
    ∃ ordered : Fin n → Piece G,
      (∀ i, (ordered i).start = route ⟨2 * i.val, by have hi := i.isLt; omega⟩ ∧
        (ordered i).finish = route ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩) ∧
      (∀ v, ((List.ofFn ordered).flatMap fun z => z.walk.support).count v = 1) ∧
      (∀ e, e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
        e ∈ w.edgeSet ∧ e ∉ E) := by
  obtain ⟨_, hcount, hedges, hlength⟩ := cyclePieces_spec E w hw hE hcuts
  exact actual_partition_pieces_reordered E w (cyclePieces E w hw hE hcuts) n
    hcount hedges (hlength.trans hcard) route hmatch

#print axioms actual_cycle_slices_reordered

private theorem linked_of_getElem (p : Piece G) (ps : List (Piece G))
    (h : ∀ i (hi : i + 1 < (p :: ps).length),
      G.Adj ((p :: ps)[i]'(by omega)).finish ((p :: ps)[i + 1]'hi).start) :
    Linked p ps := by
  induction ps generalizing p with
  | nil => trivial
  | cons q qs ih =>
    refine ⟨?_, ih q ?_⟩
    · simpa only [Nat.zero_add, List.getElem_cons_zero, List.getElem_cons_succ] using
        h 0 (by simp only [List.length_cons]; omega)
    · intro i hi
      simpa only [List.getElem_cons_succ, Nat.add_assoc] using
        h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)

private theorem finish_eq_last (p : Piece G) (ps : List (Piece G)) :
    finish p ps = ((p :: ps).getLast (by simp)).finish := by
  induction ps generalizing p with
  | nil => rfl
  | cons q qs ih =>
    simpa only [finish, List.getLast_cons_cons] using ih q

/-- Real connectors expand the permutation into a real Hamilton path on
the original child vertex type. Its support is precisely the joined actual
piece supports; its edges are precisely the actual chain inventory. -/
theorem actual_partition_pieces_joined (E : Finset (Sym2 V)) {a : V}
    (w : G.Walk a a) (pieces : List (Piece G)) (n : ℕ)
    (hcount : ∀ v, (pieces.flatMap fun z => z.walk.support).count v = 1)
    (hedges : ∀ e, e ∈ pieces.flatMap (fun z => z.walk.edges) ↔
      e ∈ w.edgeSet ∧ e ∉ E) (hlen : pieces.length = n + 1)
    (route : Fin (2 * (n + 1)) → V)
    (hmatch : ∀ z ∈ pieces,
      ∃ i : Fin (n + 1), s(z.start, z.finish) = routeEdge route i)
    (hlinks : ∀ i (hi : i + 1 < n + 1),
      G.Adj (route ⟨2 * i + 1, by omega⟩) (route ⟨2 * (i + 1), by omega⟩)) :
    ∃ ordered : Fin (n + 1) → Piece G,
      ∃ q : G.Walk (route ⟨0, by omega⟩) (route ⟨2 * (n + 1) - 1, by omega⟩),
      q.IsHamiltonian ∧
      (∀ i, (ordered i).start = route ⟨2 * i.val, by have hi := i.isLt; omega⟩ ∧
        (ordered i).finish = route ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩) ∧
      q.support = (List.ofFn ordered).flatMap (fun z => z.walk.support) ∧
      q.edges = chainEdges (ordered 0) (List.ofFn fun i : Fin n => ordered i.succ) ∧
      ∀ e, e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
        e ∈ w.edgeSet ∧ e ∉ E := by
  obtain ⟨ordered, hend, hcount, hedges⟩ :=
    actual_partition_pieces_reordered E w pieces (n + 1) hcount hedges hlen route hmatch
  let p := ordered 0
  let ps := List.ofFn fun i : Fin n => ordered i.succ
  have hlist : p :: ps = List.ofFn ordered := (List.ofFn_succ (f := ordered)).symm
  have hlink : Linked p ps := by
    have hindexed : ∀ i (hi : i + 1 < (List.ofFn ordered).length),
        G.Adj ((List.ofFn ordered)[i]'(by omega)).finish
          ((List.ofFn ordered)[i + 1]'hi).start := by
      intro i hi
      simp only [List.length_ofFn] at hi
      simp only [List.getElem_ofFn]
      rw [(hend ⟨i, by omega⟩).2, (hend ⟨i + 1, hi⟩).1]
      exact hlinks i hi
    apply linked_of_getElem
    simpa only [hlist] using hindexed
  have hs : p.start = route ⟨0, by omega⟩ := (hend 0).1
  have hf : finish p ps = route ⟨2 * (n + 1) - 1, by omega⟩ := by
    rw [finish_eq_last]
    have hlastList : ((List.ofFn ordered).getLast (by simp)).finish =
        route ⟨2 * (n + 1) - 1, by omega⟩ := by
      rw [List.getLast_ofFn]
      have hlast : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp only [Fin.val_mk, Fin.val_last]; omega)
      rw [hlast, (hend (Fin.last n)).2]
      congr 1
    simpa only [hlist] using hlastList
  let q := (join p ps hlink).copy hs hf
  refine ⟨ordered, q, ?_, hend, ?_, ?_, hedges⟩
  · intro v
    simpa only [q, SimpleGraph.Walk.support_copy, join_support, hlist] using hcount v
  · simp only [q, SimpleGraph.Walk.support_copy, join_support, hlist]
  · simp only [q, SimpleGraph.Walk.edges_copy, join_edges, p, ps]

/-- Real connectors expand the permutation into a real Hamilton path on
the original child vertex type. Its support is precisely the joined actual
piece supports; its edges are precisely the actual chain inventory. -/
theorem actual_cycle_slices_joined (E : Finset (Sym2 V)) {a : V}
    (w : G.Walk a a) (hw : w.IsHamiltonianCycle) (hE : E.Nonempty)
    (hcuts : ∀ e ∈ E, e ∈ w.edgeSet) (n : ℕ) (hcard : E.card = n + 1)
    (route : Fin (2 * (n + 1)) → V)
    (hmatch : ∀ z ∈ cyclePieces E w hw hE hcuts,
      ∃ i : Fin (n + 1), s(z.start, z.finish) = routeEdge route i)
    (hlinks : ∀ i (hi : i + 1 < n + 1),
      G.Adj (route ⟨2 * i + 1, by omega⟩) (route ⟨2 * (i + 1), by omega⟩)) :
    ∃ ordered : Fin (n + 1) → Piece G,
      ∃ q : G.Walk (route ⟨0, by omega⟩) (route ⟨2 * (n + 1) - 1, by omega⟩),
      q.IsHamiltonian ∧
      (∀ i, (ordered i).start = route ⟨2 * i.val, by have hi := i.isLt; omega⟩ ∧
        (ordered i).finish = route ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩) ∧
      q.support = (List.ofFn ordered).flatMap (fun z => z.walk.support) ∧
      q.edges = chainEdges (ordered 0) (List.ofFn fun i : Fin n => ordered i.succ) ∧
      ∀ e, e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
        e ∈ w.edgeSet ∧ e ∉ E := by
  obtain ⟨_, hcount, hedges, hlength⟩ := cyclePieces_spec E w hw hE hcuts
  exact actual_partition_pieces_joined E w (cyclePieces E w hw hE hcuts) n
    hcount hedges (hlength.trans hcard) route hmatch hlinks

#print axioms actual_cycle_partition_inventory
#print axioms actual_partition_pieces_reordered
#print axioms actual_partition_pieces_joined
#print axioms actual_cycle_slices_joined

end D5.S3.Combinatorics.Graph.Walks.ActualCyclePieceReordering

/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2HalfRestoration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual half-cut restoration earns both native B2 component tables. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Components

/- Restore precisely the opposite three actual cuts. The barred B2^1 endpoint
exception retains its original native indexing. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2HalfRestoration

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Components
open D5.S3.Combinatorics.Graph.Walks.LeafNonbacktrackingComponent
open private below_cycle_degree below_cycle_missing_neighbor markedCut_injective
  surviving_adj_iff from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingModel
open private leaf_in_path_is_endpoint from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SixthComponent

def HalfCut (m : ℕ) (side : Bool) (e : Sym2 (Configuration m)) : Prop :=
  ∃ i : Fin 3, e = markedEdge m (i, side)

def HalfEdge (m : ℕ) (side : Bool) (e : Sym2 (Configuration m)) : Prop :=
  ((F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) ∧ ¬ HalfCut m side e

def halfGraph (m : ℕ) (side : Bool) : SimpleGraph (Configuration m) :=
  SimpleGraph.fromEdgeSet {e | HalfEdge m side e}

def halfStart (side : Bool) (i : Fin 3) : Fin 3 × Bool × Bool :=
  if side then
    match i.val with
    | 0 => (0, true, false)
    | 1 => (1, true, true)
    | _ => (2, true, true)
  else
    match i.val with
    | 0 => (0, false, false)
    | 1 => (0, false, true)
    | _ => (1, false, false)

def halfFinish (side : Bool) (i : Fin 3) : Fin 3 × Bool × Bool :=
  if side then
    match i.val with
    | 0 => (1, true, false)
    | 1 => (2, true, false)
    | _ => (0, true, true)
  else
    match i.val with
    | 0 => (2, false, false)
    | 1 => (1, false, true)
    | _ => (2, false, true)

private theorem half_adj_iff (m : ℕ) (side : Bool) (x y : Configuration m) :
    (halfGraph m side).Adj x y ↔ HalfEdge m side s(x, y) ∧ x ≠ y :=
  SimpleGraph.fromEdgeSet_adj _

private theorem surviving_le_half (m : ℕ) (side : Bool) :
    survivingGraph m ≤ halfGraph m side := by
  intro x y hxy
  obtain ⟨⟨hinv, hcut⟩, hne⟩ := (surviving_adj_iff m x y).mp hxy
  refine (half_adj_iff m side x y).mpr ⟨⟨hinv, ?_⟩, hne⟩
  rintro ⟨i, hi⟩
  exact hcut ⟨(i, side), hi⟩

private theorem actual_half_cycle_model {m : ℕ} (hm : 5 ≤ m) (side : Bool) :
    ∃ baseVertex : Configuration m,
      ∃ p : (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Walk
          baseVertex baseVertex,
        p.IsCycle ∧
        (∀ x y, (halfGraph m side).Adj x y → p.toSubgraph.Adj x y) ∧
        (∀ x, x ∈ p.support ↔ F2Domain m x) ∧
        (∀ q : Fin 3 × Bool, markedEdge m q ∈ p.edges) ∧
        ∀ e, e ∈ p.edges ↔
          (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e := by
  obtain ⟨base, w, hw, hinv, _, hmarked⟩ :=
    native_j2_hamiltonian_cycle_with_marked_edges hm
  let f : domainGraph (F2Domain m) →g
      SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m)) :=
    ⟨Subtype.val, fun h => h⟩
  have hf : (f : {x : Configuration m // F2Domain m x} → Configuration m) =
      Subtype.val := rfl
  let p := w.map f
  have hedges : p.edges = w.edges.map (Sym2.map Subtype.val) := by
    exact SimpleGraph.Walk.edges_map f w
  refine ⟨base.val, p, hw.isCycle.map Subtype.val_injective, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr
    rw [hedges]
    exact (hinv _).mpr ((half_adj_iff m side x y).mp hxy).1.1
  · intro x
    rw [show p.support = w.support.map Subtype.val by
      simp only [p, SimpleGraph.Walk.support_map, hf]]
    constructor
    · intro hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact v.property
    · intro hx
      exact List.mem_map.mpr ⟨⟨x, hx⟩, hw.mem_support _, rfl⟩
  · intro q
    rw [hedges]
    exact hmarked q
  · intro e
    rw [hedges]
    exact hinv e

private theorem actual_half_degree {m : ℕ} (hm : 5 ≤ m) (side : Bool) :
    ∀ x, ((halfGraph m side).neighborSet x).ncard ≤ 2 := by
  obtain ⟨a, p, hp, hsub, _, _, _⟩ := actual_half_cycle_model hm side
  exact below_cycle_degree p hp hsub

private theorem actual_half_leaf {m : ℕ} (hm : 5 ≤ m) (side : Bool)
    (i : Fin 3) (left : Bool) :
    ((halfGraph m side).neighborSet (port m (i, side, left))).Subsingleton := by
  classical
  obtain ⟨a, p, hp, hsub, _, hmarked, _⟩ := actual_half_cycle_model hm side
  let y := port m (i, side, !left)
  have he : s(port m (i, side, left), y) = markedEdge m (i, side) := by
    cases left
    · rfl
    · exact Sym2.eq_swap
  apply below_cycle_missing_neighbor p hp hsub
  · apply SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr
    rw [he]
    exact hmarked (i, side)
  · intro hadj
    exact ((half_adj_iff m side _ _).mp hadj).1.2 ⟨i, he⟩

private theorem actual_half_port_leaf {m : ℕ} (hm : 5 ≤ m) (side : Bool)
    (q : Fin 3 × Bool × Bool) (hq : q.2.1 = side) :
    ((halfGraph m side).neighborSet (port m q)).Subsingleton := by
  rcases q with ⟨i, tag, left⟩
  dsimp at hq
  subst tag
  exact actual_half_leaf hm side i left

private theorem actual_restored_cut {m : ℕ} (hm : 5 ≤ m) (side : Bool) (i : Fin 3) :
    (halfGraph m side).Adj
      (port m (i, !side, false)) (port m (i, !side, true)) := by
  obtain ⟨_, _, _, hinv, _, hmarked⟩ := native_j2_hamiltonian_cycle_with_marked_edges hm
  apply (half_adj_iff m side _ _).mpr
  refine ⟨⟨(hinv _).mp (hmarked (i, !side)), ?_⟩, ?_⟩
  · rintro ⟨j, hj⟩
    change markedEdge m (i, !side) = markedEdge m (j, side) at hj
    have he := congrArg Prod.snd (markedCut_injective hm hj)
    cases side <;> cases he
  · intro he
    have h := congrArg (fun q : Fin 3 × Bool × Bool => q.2.2)
      (native_j2_port_injective hm he)
    cases h

private theorem half_reach_data {m : ℕ} (hm : 5 ≤ m) (side : Bool) :
    (∀ i : Fin 3, (halfGraph m side).Reachable
      (port m (halfStart side i)) (port m (halfFinish side i))) ∧
    ∀ j : Fin 6, ∃ i : Fin 3, (halfGraph m side).Reachable
      (port m (halfStart side i)) (port m (componentStartPort j)) := by
  obtain ⟨paths, _, _, _, _⟩ := native_j2_six_component_partition hm
  have r0 := (paths 0).reachable.mono (surviving_le_half m side)
  have r1 := (paths 1).reachable.mono (surviving_le_half m side)
  have r2 := (paths 2).reachable.mono (surviving_le_half m side)
  have r3 := (paths 3).reachable.mono (surviving_le_half m side)
  have r4 := (paths 4).reachable.mono (surviving_le_half m side)
  have r5 := (paths 5).reachable.mono (surviving_le_half m side)
  have c0 := (actual_restored_cut hm side 0).reachable
  have c1 := (actual_restored_cut hm side 1).reachable
  have c2 := (actual_restored_cut hm side 2).reachable
  cases side
  · have hL := r1.trans (c1.symm.trans (r4.symm.trans (c0.trans r5.symm)))
    have hR := r2.trans (c2.symm.trans r3.symm)
    constructor
    · intro i
      fin_cases i
      · exact r0
      · exact hL
      · exact hR
    · intro j
      fin_cases j
      · exact ⟨0, .rfl⟩
      · exact ⟨1, .rfl⟩
      · exact ⟨2, .rfl⟩
      · exact ⟨2, hR⟩
      · exact ⟨1, r1.trans (c1.symm.trans r4.symm)⟩
      · exact ⟨1, hL⟩
  · have hL := r1.symm.trans (c0.symm.trans (r0.trans (c2.trans r3)))
    have hR := r2.symm.trans (c1.trans r5)
    constructor
    · intro i
      fin_cases i
      · exact r4
      · exact hL
      · exact hR
    · intro j
      fin_cases j
      · exact ⟨1, r1.symm.trans c0.symm⟩
      · exact ⟨1, r1.symm⟩
      · exact ⟨2, r2.symm⟩
      · exact ⟨1, r1.symm.trans (c0.symm.trans (r0.trans c2))⟩
      · exact ⟨0, .rfl⟩
      · exact ⟨2, r2.symm.trans c1⟩

/-- Restore the opposite three cuts of the actual joint J2 graph. Both
native one-frame boundary tables are conclusions, including barred B2^1. -/
theorem native_j2_half_component_partition {m : ℕ} (hm : 5 ≤ m) (side : Bool) :
    ∃ paths : (i : Fin 3) → (halfGraph m side).Walk
        (port m (halfStart side i)) (port m (halfFinish side i)),
      (∀ i, (paths i).IsPath) ∧
      (∀ i x, x ∈ (paths i).support ↔
        (halfGraph m side).Reachable (port m (halfStart side i)) x) ∧
      (∀ i x y, (halfGraph m side).Adj x y ∧
        (halfGraph m side).Reachable (port m (halfStart side i)) x ↔
          s(x, y) ∈ (paths i).edges) ∧
      (∀ x, F2Domain m x ↔ ∃! i, x ∈ (paths i).support) ∧
      ∀ e, e ∈ (List.ofFn fun i => (paths i).edges).flatten ↔ HalfEdge m side e := by
  classical
  obtain ⟨hpair, hbridge⟩ := half_reach_data hm side
  have hsig : ∀ i j : Fin 3,
      halfStart side j = halfStart side i ∨ halfStart side j = halfFinish side i → j = i := by
    cases side <;> decide
  have hside : ∀ i : Fin 3,
      (halfStart side i).2.1 = side ∧ (halfFinish side i).2.1 = side := by
    cases side <;> decide
  have hdistinct : ∀ i : Fin 3, halfStart side i ≠ halfFinish side i := by
    cases side <;> decide
  have hpaths : ∀ i : Fin 3,
      ∃ w : (halfGraph m side).Walk
          (port m (halfStart side i)) (port m (halfFinish side i)),
        w.IsPath ∧
        (∀ x, x ∈ w.support ↔ (halfGraph m side).Reachable
          (port m (halfStart side i)) x) ∧
        ∀ x y, (halfGraph m side).Adj x y ∧
          (halfGraph m side).Reachable (port m (halfStart side i)) x ↔ s(x, y) ∈ w.edges := by
    intro i
    obtain ⟨w, hp⟩ := (hpair i).exists_isPath
    have hne : port m (halfStart side i) ≠ port m (halfFinish side i) :=
      fun h => hdistinct i (native_j2_port_injective hm h)
    have hnil : ¬w.Nil := fun h => hne h.eq
    have hnb : Nonbacktracking w := by
      intro n hn he
      have h := hp.getVert_injOn (show n ≤ w.length by omega) hn he
      omega
    have ha := actual_half_port_leaf hm side (halfStart side i) (hside i).1
    have hb := actual_half_port_leaf hm side (halfFinish side i) (hside i).2
    obtain ⟨hp', _, _, _, hv, he⟩ :=
      nonbacktracking_leaf_full_component w (actual_half_degree hm side) ha hb hnil hnb
    exact ⟨w, hp', hv, he⟩
  choose paths hpath hvertices hedges using hpaths
  obtain ⟨six, _, hsixvertices, _, hsixdomain⟩ := native_j2_six_component_partition hm
  obtain ⟨a, p, hp, hsub, hdomain, _, hinventory⟩ := actual_half_cycle_model hm side
  have hdomadj (x y : Configuration m) (hxy : (halfGraph m side).Adj x y) :
      F2Domain m y :=
    (hdomain y).mp (p.snd_mem_support_of_mem_edges
      (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp (hsub x y hxy)))
  have hpreserve (y x : Configuration m) (hy : F2Domain m y)
      (hr : (halfGraph m side).Reachable y x) : F2Domain m x := by
    obtain ⟨w⟩ := hr
    revert hy
    induction w with
    | nil => exact fun h => h
    | @cons a b c h w ih => exact fun _ => ih (hdomadj a b h)
  have hcover : ∀ x, F2Domain m x ↔ ∃! i, x ∈ (paths i).support := by
    intro x
    constructor
    · intro hx
      obtain ⟨j, hxj, _⟩ := (hsixdomain x).mp hx
      obtain ⟨i, hi⟩ := hbridge j
      have hix := (hvertices i x).mpr
        (hi.trans (((hsixvertices j x).mp hxj).mono (surviving_le_half m side)))
      refine ⟨i, hix, ?_⟩
      intro j hj
      have hr := ((hvertices i x).mp hix).trans ((hvertices j x).mp hj).symm
      have ha := actual_half_port_leaf hm side (halfStart side j) (hside j).1
      rcases leaf_in_path_is_endpoint (paths i) (hpath i)
          ((hvertices i _).mpr hr) ha with he | he
      · exact hsig i j (Or.inl (native_j2_port_injective hm he))
      · exact hsig i j (Or.inr (native_j2_port_injective hm he))
    · rintro ⟨i, hi, _⟩
      exact hpreserve _ x (native_j2_port_domain hm (halfStart side i))
        ((hvertices i x).mp hi)
  -- The exact component inventory now yields the independent flattened inventory.
  refine ⟨paths, hpath, hvertices, hedges, hcover, ?_⟩
  intro e
  refine Sym2.inductionOn e ?_
  intro x y
  constructor
  · intro he
    obtain ⟨es, hes, he⟩ := List.mem_flatten.mp he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hes
    exact ((half_adj_iff m side x y).mp ((hedges i x y).mpr he).1).1
  · intro he
    have horiginal : s(x, y) ∈ p.edges := (hinventory _).mpr he.1
    have hsource := SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr horiginal
    have hxy : (halfGraph m side).Adj x y :=
      (half_adj_iff m side x y).mpr ⟨he, hsource.adj_sub.ne⟩
    have hx : F2Domain m x :=
      (hdomain x).mp (p.fst_mem_support_of_mem_edges horiginal)
    obtain ⟨i, hi, _⟩ := (hcover x).mp hx
    exact List.mem_flatten.mpr ⟨(paths i).edges, List.mem_ofFn.mpr ⟨i, rfl⟩,
      (hedges i x y).mp ⟨hxy, (hvertices i x).mp hi⟩⟩

#print axioms native_j2_half_component_partition

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2HalfRestoration

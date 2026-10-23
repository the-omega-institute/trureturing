/- GID: D5/S3/Combinatorics/Graph/Walks/ActualSingleOrderBoundaryUpdate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualSingleOrderBoundaryUpdate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal replacement of the old joint path constructs complete single-order boundaries with exact actual inventories and endpoint updates. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.Walks.ActualJointPartitionUpdate
import D5.S3.Combinatorics.Graph.Walks.ActualJointEndpointPairs

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualSingleOrderBoundaryUpdate

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualJointEndpointPairs
open private filter_complement_of_nodup pieces_support_length from
  D5.S3.Combinatorics.Graph.Walks.ActualJointPartitionUpdate
open private actual_distinguished_pair_absent_from_rest from
  D5.S3.Combinatorics.Graph.Walks.ActualJointEndpointPairs

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- A literal old full-boundary route is split around the actual joint
path d. Restoring l1--r1 in the already constructed next joint state gives
l0--y and r0--x; every other old full-boundary path remains unchanged.
The source inventory partitions restored old marks from still-deleted
marks of the same next cycle, so no source supplier edge is reintroduced. -/
theorem actual_single_order_boundary_update
    {base x ℓ z y ℓ₀ r₀ ℓ₁ r₁ : V}
    (c : G.Walk base base) (hc : c.IsHamiltonianCycle)
    (d : G.Walk ℓ z) (front : G.Walk x ℓ) (tail : G.Walk z y)
    (old : G.Walk x y) (hold : old = front.append (d.append tail))
    (oldrest jointrest : List (Piece G))
    (holdNodup : (old.support ++ oldrest.flatMap fun p => p.walk.support).Nodup)
    (holdSupport : (old.support ++ oldrest.flatMap fun p => p.walk.support).Perm
      (d.support ++ jointrest.flatMap fun p => p.walk.support))
    (restored deleted : List (Sym2 V))
    (holdEdges : (old.edges ++ oldrest.flatMap fun p => p.walk.edges).Perm
      (d.edges ++ (jointrest.flatMap fun p => p.walk.edges) ++ restored))
    (new₀ : G.Walk z ℓ₀) (new₁ : G.Walk r₀ ℓ₁) (new₂ : G.Walk r₁ ℓ)
    (hrestore : G.Adj ℓ₁ r₁)
    (hcurrentSupport : c.support.tail.Perm
      (new₀.support ++ new₁.support ++ new₂.support ++
        jointrest.flatMap fun p => p.walk.support))
    (hcurrentEdges : c.edges.Perm
      (new₀.edges ++ new₁.edges ++ new₂.edges ++
        (jointrest.flatMap fun p => p.walk.edges) ++ restored ++
        [s(ℓ₁, r₁)] ++ deleted)) :
    ∃ boundary₀ : G.Walk ℓ₀ y, ∃ boundary₁ : G.Walk r₀ x,
      let pieces : List (Piece G) := [⟨ℓ₀, y, boundary₀⟩, ⟨r₀, x, boundary₁⟩] ++ oldrest
      let cuts := deleted.toFinset
      (∀ p ∈ pieces, p.walk.IsPath) ∧
      (∀ v, (pieces.flatMap fun p => p.walk.support).count v = 1) ∧
      (pieces.flatMap fun p => p.walk.support).Perm c.support.tail ∧
      (pieces.flatMap fun p => p.walk.edges).Perm
        (c.edges.filter fun e => decide (e ∉ cuts)) ∧
      (∀ e, e ∈ (pieces.flatMap fun p => p.walk.edges) ↔
        e ∈ c.edgeSet ∧ e ∉ cuts) ∧
      (∀ e ∈ cuts, e ∈ c.edgeSet) ∧ pieces.length = cuts.card ∧
      endpointPairs pieces =
        (endpointPairs (⟨x, y, old⟩ :: oldrest)).erase s(x, y) ∪ {s(ℓ₀, y), s(r₀, x)} ∧
      boundary₀ = new₀.reverse.append tail ∧
      boundary₁ = (new₁.append (new₂.cons hrestore)).append front.reverse := by
  classical
  let boundary₀ : G.Walk ℓ₀ y := new₀.reverse.append tail
  let boundary₁ : G.Walk r₀ x := (new₁.append (new₂.cons hrestore)).append front.reverse
  let pieces : List (Piece G) := [⟨ℓ₀, y, boundary₀⟩, ⟨r₀, x, boundary₁⟩] ++ oldrest
  let cuts := deleted.toFinset
  have hscount (v : V) :
      (tail.support.tail ++ front.reverse.support.tail ++
        oldrest.flatMap fun p => p.walk.support).count v =
        (jointrest.flatMap fun p => p.walk.support).count v := by
    have hs := holdSupport.count_eq v
    rw [hold, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.tail_support_append] at hs
    have hp := congrArg (List.count v) (SimpleGraph.Walk.cons_tail_support front.reverse)
    rw [SimpleGraph.Walk.support_reverse, List.count_reverse] at hp
    have hd := congrArg (List.count v) (SimpleGraph.Walk.cons_tail_support d)
    simp only [SimpleGraph.Walk.support_reverse, List.count_reverse,
      List.count_append, List.count_cons] at hs hp hd ⊢
    omega
  have hsupport : (pieces.flatMap fun p => p.walk.support).Perm c.support.tail := by
    apply List.perm_iff_count.mpr
    intro v
    have hs := hcurrentSupport.count_eq v
    have hold := hscount v
    simp only [pieces, boundary₀, boundary₁, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
      List.tail_cons, SimpleGraph.Walk.support_reverse, List.count_append,
      List.count_reverse] at hs hold ⊢
    omega
  have hcount (v : V) : (pieces.flatMap fun p => p.walk.support).count v = 1 := by
    rw [hsupport.count_eq v]
    exact (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mp hc).2 v
  have hn : (pieces.flatMap fun p => p.walk.support).Nodup :=
    List.nodup_iff_count_le_one.mpr (fun v => by rw [hcount v])
  have hpaths (p : Piece G) (hp : p ∈ pieces) : p.walk.IsPath :=
    SimpleGraph.Walk.IsPath.mk' ((List.nodup_flatMap.mp hn).1 p hp)
  have hecounts (e : Sym2 V) :
      (front.edges ++ tail.edges ++ oldrest.flatMap fun p => p.walk.edges).count e =
        ((jointrest.flatMap fun p => p.walk.edges) ++ restored).count e := by
    have he := holdEdges.count_eq e
    rw [hold, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append] at he
    simp only [List.count_append] at he ⊢
    omega
  have hedges : c.edges.Perm ((pieces.flatMap fun p => p.walk.edges) ++ deleted) := by
    apply hcurrentEdges.trans
    apply List.perm_iff_count.mpr
    intro e
    have hold := hecounts e
    simp only [pieces, boundary₀, boundary₁, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_reverse, List.count_append, List.count_reverse,
      List.count_cons, List.count_nil] at hold ⊢
    omega
  have hened : ((pieces.flatMap fun p => p.walk.edges) ++ deleted).Nodup :=
    hedges.nodup_iff.mp hc.isCycle.isTrail.edges_nodup
  have hdeletedNodup : deleted.Nodup := (List.nodup_append'.mp hened).2.1
  have hfiltered : (c.edges.filter fun e => decide (e ∉ cuts)).Perm
      (pieces.flatMap fun p => p.walk.edges) := by
    have h := List.Perm.filter (fun e => decide (e ∉ cuts)) hedges
    simpa only [cuts, filter_complement_of_nodup _ _ hened] using h
  have hcuts (e : Sym2 V) (he : e ∈ cuts) : e ∈ c.edgeSet := by
    change e ∈ c.edges
    exact hedges.mem_iff.mpr (List.mem_append.mpr (Or.inr (List.mem_toFinset.mp he)))
  have hcard : pieces.length = cuts.card := by
    have hslen := hsupport.length_eq
    have helen := hedges.length_eq
    have hplen := pieces_support_length pieces
    have hrcard : cuts.card = deleted.length := List.toFinset_card_of_nodup hdeletedNodup
    simp only [List.length_tail, SimpleGraph.Walk.length_support,
      List.length_append, SimpleGraph.Walk.length_edges] at hslen helen
    rw [hrcard]
    omega
  have hpairs : endpointPairs pieces =
      (endpointPairs (⟨x, y, old⟩ :: oldrest)).erase s(x, y) ∪ {s(ℓ₀, y), s(r₀, x)} := by
    have hnot := actual_distinguished_pair_absent_from_rest old oldrest holdNodup
    have herase : (endpointPairs (⟨x, y, old⟩ :: oldrest)).erase s(x, y) =
        endpointPairs oldrest := by
      simp only [endpointPairs, List.map_cons, List.toFinset_cons]
      change (insert s(x, y) (endpointPairs oldrest)).erase s(x, y) = endpointPairs oldrest
      exact Finset.erase_insert hnot
    rw [herase]
    change endpointPairs ([_, _] ++ oldrest) = endpointPairs oldrest ∪ {_ , _}
    simp only [endpointPairs, List.map_append, List.map_cons, List.map_nil,
      List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
    exact Finset.union_comm _ _
  refine ⟨boundary₀, boundary₁, hpaths, hcount, hsupport, hfiltered.symm, ?_,
    hcuts, hcard, hpairs, rfl, rfl⟩
  intro e
  rw [← hfiltered.mem_iff]
  simp only [List.mem_filter, decide_eq_true_eq, SimpleGraph.Walk.mem_edgeSet]
  rfl

/-- Restoring the first Q zero cut gives the other actual single-order
boundary. The restored edge joins new₁.reverse to new₀.reverse on the z
side of the old distinguished path; new₂ retains its l side. All old
paths outside that route remain unchanged. Both the exhaustiveness and
exact retained-edge inventory are earned on the same actual cycle. -/
theorem actual_single_order_first_cut_boundary_update
    {base x ℓ z y ℓ₀ r₀ ℓ₁ r₁ : V}
    (c : G.Walk base base) (hc : c.IsHamiltonianCycle)
    (d : G.Walk ℓ z) (front : G.Walk x ℓ) (tail : G.Walk z y)
    (old : G.Walk x y) (hold : old = front.append (d.append tail))
    (oldrest jointrest : List (Piece G))
    (holdNodup : (old.support ++ oldrest.flatMap fun p => p.walk.support).Nodup)
    (holdSupport : (old.support ++ oldrest.flatMap fun p => p.walk.support).Perm
      (d.support ++ jointrest.flatMap fun p => p.walk.support))
    (restored deleted : List (Sym2 V))
    (holdEdges : (old.edges ++ oldrest.flatMap fun p => p.walk.edges).Perm
      (d.edges ++ (jointrest.flatMap fun p => p.walk.edges) ++ restored))
    (new₀ : G.Walk z ℓ₀) (new₁ : G.Walk r₀ ℓ₁) (new₂ : G.Walk r₁ ℓ)
    (hrestore : G.Adj ℓ₀ r₀)
    (hcurrentSupport : c.support.tail.Perm
      (new₀.support ++ new₁.support ++ new₂.support ++
        jointrest.flatMap fun p => p.walk.support))
    (hcurrentEdges : c.edges.Perm
      (new₀.edges ++ new₁.edges ++ new₂.edges ++
        (jointrest.flatMap fun p => p.walk.edges) ++ restored ++
        [s(ℓ₀, r₀)] ++ deleted)) :
    ∃ boundary₀ : G.Walk ℓ₁ y, ∃ boundary₁ : G.Walk r₁ x,
      let pieces : List (Piece G) := [⟨ℓ₁, y, boundary₀⟩, ⟨r₁, x, boundary₁⟩] ++ oldrest
      let cuts := deleted.toFinset
      (∀ p ∈ pieces, p.walk.IsPath) ∧
      (∀ v, (pieces.flatMap fun p => p.walk.support).count v = 1) ∧
      (pieces.flatMap fun p => p.walk.support).Perm c.support.tail ∧
      (pieces.flatMap fun p => p.walk.edges).Perm
        (c.edges.filter fun e => decide (e ∉ cuts)) ∧
      (∀ e, e ∈ (pieces.flatMap fun p => p.walk.edges) ↔
        e ∈ c.edgeSet ∧ e ∉ cuts) ∧
      (∀ e ∈ cuts, e ∈ c.edgeSet) ∧ pieces.length = cuts.card ∧
      endpointPairs pieces =
        (endpointPairs (⟨x, y, old⟩ :: oldrest)).erase s(x, y) ∪ {s(ℓ₁, y), s(r₁, x)} ∧
      boundary₀ = (new₁.reverse.append (new₀.reverse.cons hrestore.symm)).append tail ∧
      boundary₁ = new₂.append front.reverse := by
  classical
  let boundary₀ : G.Walk ℓ₁ y := (new₁.reverse.append (new₀.reverse.cons hrestore.symm)).append tail
  let boundary₁ : G.Walk r₁ x := new₂.append front.reverse
  let pieces : List (Piece G) := [⟨ℓ₁, y, boundary₀⟩, ⟨r₁, x, boundary₁⟩] ++ oldrest
  let cuts := deleted.toFinset
  have hscount (v : V) :
      (tail.support.tail ++ front.reverse.support.tail ++
        oldrest.flatMap fun p => p.walk.support).count v =
        (jointrest.flatMap fun p => p.walk.support).count v := by
    have hs := holdSupport.count_eq v
    rw [hold, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.tail_support_append] at hs
    have hp := congrArg (List.count v) (SimpleGraph.Walk.cons_tail_support front.reverse)
    rw [SimpleGraph.Walk.support_reverse, List.count_reverse] at hp
    have hd := congrArg (List.count v) (SimpleGraph.Walk.cons_tail_support d)
    simp only [SimpleGraph.Walk.support_reverse, List.count_reverse,
      List.count_append, List.count_cons] at hs hp hd ⊢
    omega
  have hsupport : (pieces.flatMap fun p => p.walk.support).Perm c.support.tail := by
    apply List.perm_iff_count.mpr
    intro v
    have hs := hcurrentSupport.count_eq v
    have hold := hscount v
    simp only [pieces, boundary₀, boundary₁, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
      List.tail_cons, SimpleGraph.Walk.support_reverse, List.count_append,
      List.count_reverse] at hs hold ⊢
    omega
  have hcount (v : V) : (pieces.flatMap fun p => p.walk.support).count v = 1 := by
    rw [hsupport.count_eq v]
    exact (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mp hc).2 v
  have hn : (pieces.flatMap fun p => p.walk.support).Nodup :=
    List.nodup_iff_count_le_one.mpr (fun v => by rw [hcount v])
  have hpaths (p : Piece G) (hp : p ∈ pieces) : p.walk.IsPath :=
    SimpleGraph.Walk.IsPath.mk' ((List.nodup_flatMap.mp hn).1 p hp)
  have hecounts (e : Sym2 V) :
      (front.edges ++ tail.edges ++ oldrest.flatMap fun p => p.walk.edges).count e =
        ((jointrest.flatMap fun p => p.walk.edges) ++ restored).count e := by
    have he := holdEdges.count_eq e
    rw [hold, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append] at he
    simp only [List.count_append] at he ⊢
    omega
  have hswap : s(r₀, ℓ₀) = s(ℓ₀, r₀) := Sym2.eq_swap
  have hedges : c.edges.Perm ((pieces.flatMap fun p => p.walk.edges) ++ deleted) := by
    apply hcurrentEdges.trans
    apply List.perm_iff_count.mpr
    intro e
    have hold := hecounts e
    simp only [pieces, boundary₀, boundary₁, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil,
      SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_reverse, hswap, List.count_append, List.count_reverse,
      List.count_cons, List.count_nil] at hold ⊢
    omega
  have hened : ((pieces.flatMap fun p => p.walk.edges) ++ deleted).Nodup :=
    hedges.nodup_iff.mp hc.isCycle.isTrail.edges_nodup
  have hdeletedNodup : deleted.Nodup := (List.nodup_append'.mp hened).2.1
  have hfiltered : (c.edges.filter fun e => decide (e ∉ cuts)).Perm
      (pieces.flatMap fun p => p.walk.edges) := by
    have h := List.Perm.filter (fun e => decide (e ∉ cuts)) hedges
    simpa only [cuts, filter_complement_of_nodup _ _ hened] using h
  have hcuts (e : Sym2 V) (he : e ∈ cuts) : e ∈ c.edgeSet := by
    change e ∈ c.edges
    exact hedges.mem_iff.mpr (List.mem_append.mpr (Or.inr (List.mem_toFinset.mp he)))
  have hcard : pieces.length = cuts.card := by
    have hslen := hsupport.length_eq
    have helen := hedges.length_eq
    have hplen := pieces_support_length pieces
    have hrcard : cuts.card = deleted.length := List.toFinset_card_of_nodup hdeletedNodup
    simp only [List.length_tail, SimpleGraph.Walk.length_support,
      List.length_append, SimpleGraph.Walk.length_edges] at hslen helen
    rw [hrcard]
    omega
  have hpairs : endpointPairs pieces =
      (endpointPairs (⟨x, y, old⟩ :: oldrest)).erase s(x, y) ∪ {s(ℓ₁, y), s(r₁, x)} := by
    have hnot := actual_distinguished_pair_absent_from_rest old oldrest holdNodup
    have herase : (endpointPairs (⟨x, y, old⟩ :: oldrest)).erase s(x, y) =
        endpointPairs oldrest := by
      simp only [endpointPairs, List.map_cons, List.toFinset_cons]
      change (insert s(x, y) (endpointPairs oldrest)).erase s(x, y) = endpointPairs oldrest
      exact Finset.erase_insert hnot
    rw [herase]
    change endpointPairs ([_, _] ++ oldrest) = endpointPairs oldrest ∪ {_ , _}
    simp only [endpointPairs, List.map_append, List.map_cons, List.map_nil,
      List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
    exact Finset.union_comm _ _
  refine ⟨boundary₀, boundary₁, hpaths, hcount, hsupport, hfiltered.symm, ?_,
    hcuts, hcard, hpairs, rfl, rfl⟩
  intro e
  rw [← hfiltered.mem_iff]
  simp only [List.mem_filter, decide_eq_true_eq, SimpleGraph.Walk.mem_edgeSet]
  rfl

#print axioms actual_single_order_boundary_update
#print axioms actual_single_order_first_cut_boundary_update

end D5.S3.Combinatorics.Graph.Walks.ActualSingleOrderBoundaryUpdate

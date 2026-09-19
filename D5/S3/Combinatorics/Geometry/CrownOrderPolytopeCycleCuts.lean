/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration]
   utility: none
   digest: Connected cycle partitions are reconstructed exactly from their boundary cuts. -/

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic
import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open D5.S3.Combinatorics.Geometry.CrownOrderPolytope

private theorem cycleGraph_adj_values {N : ℕ} (u v : Fin N)
    (hadj : (SimpleGraph.cycleGraph N).Adj u v) :
    u.val = v.val + 1 ∨ v.val = u.val + 1 ∨
      (u.val = 0 ∧ v.val = N - 1) ∨ (v.val = 0 ∧ u.val = N - 1) := by
  rw [SimpleGraph.cycleGraph_adj'] at hadj
  rcases hadj with huv | hvu
  · by_cases hvleu : v ≤ u
    · left
      have hdiff : u.val - v.val = 1 := by
        simpa [Fin.sub_val_of_le hvleu] using huv
      omega
    · right
      right
      left
      have hcast : ((u - v).val : ℤ) = 1 := congrArg Int.ofNat huv
      rw [Fin.intCast_val_sub_eq_sub_add_ite] at hcast
      simp [show ¬v ≤ u from hvleu] at hcast
      constructor <;> omega
  · by_cases hulev : u ≤ v
    · right
      left
      have hdiff : v.val - u.val = 1 := by
        simpa [Fin.sub_val_of_le hulev] using hvu
      omega
    · right
      right
      right
      have hcast : ((v - u).val : ℤ) = 1 := congrArg Int.ofNat hvu
      rw [Fin.intCast_val_sub_eq_sub_add_ite] at hcast
      simp [show ¬u ≤ v from hulev] at hcast
      constructor <;> omega

/-- The cycle edges internal to the blocks of a vertex partition. -/
def cyclePartitionGraph {N : ℕ} (s : Setoid (Fin N)) : SimpleGraph (Fin N) where
  Adj u v := s.r u v ∧ (SimpleGraph.cycleGraph N).Adj u v
  symm.symm _ _ h := ⟨s.symm h.1, h.2.symm⟩
  loopless.irrefl _ h := h.2.ne rfl

/-- A partition whose blocks induce connected subgraphs of the cycle. -/
structure ConnectedCyclePartition (N : ℕ) where
  toSetoid : Setoid (Fin N)
  connected : ∀ {u v}, toSetoid.r u v → (cyclePartitionGraph toSetoid).Reachable u v

private theorem cyclePartitionGraph_reachable_iff {N : ℕ} (P : ConnectedCyclePartition N)
    (u v : Fin N) :
    (cyclePartitionGraph P.toSetoid).Reachable u v ↔ P.toSetoid.r u v := by
  refine ⟨?_, P.connected⟩
  rintro ⟨p⟩
  induction p with
  | nil => exact P.toSetoid.refl _
  | @cons a b c hab _ ih => exact P.toSetoid.trans hab.1 ih

/-- The cyclic edges crossing between distinct blocks, indexed by their first endpoint. -/
noncomputable def cycleBoundaryCuts {N : ℕ} [NeZero N]
    (P : ConnectedCyclePartition N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun u => ¬ P.toSetoid.r u (u + 1)

/-- Delete the cyclic edges indexed by a cut set. -/
private def cycleGraphWithCuts {N : ℕ} [NeZero N]
    (cuts : Finset (Fin N)) : SimpleGraph (Fin N) where
  Adj u v := (SimpleGraph.cycleGraph N).Adj u v ∧
    ¬ ((u ∈ cuts ∧ v = u + 1) ∨ (v ∈ cuts ∧ u = v + 1))
  symm.symm _ _ h := ⟨h.1.symm, by simpa [or_comm] using h.2⟩
  loopless.irrefl u h := h.1.ne rfl

/-- The connected-component partition obtained after making the prescribed cyclic cuts. -/
private def connectedCyclePartitionOfCuts {N : ℕ} [NeZero N] (cuts : Finset (Fin N)) :
    ConnectedCyclePartition N where
  toSetoid := (cycleGraphWithCuts cuts).reachableSetoid
  connected h := h.mono fun _ _ hadj => ⟨hadj.reachable, hadj.1⟩

private theorem cycleGraphWith_boundaryCuts {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (P : ConnectedCyclePartition N) :
    cycleGraphWithCuts (cycleBoundaryCuts P) = cyclePartitionGraph P.toSetoid := by
  ext u v
  constructor
  · rintro ⟨huv, hcut⟩
    refine ⟨?_, huv⟩
    rw [SimpleGraph.cycleGraph_adj'] at huv
    rcases huv with huv | huv
    · have hpred : u = v + 1 := by
        apply (sub_eq_iff_eq_add').mp
        apply Fin.ext
        change (u - v).val = 1 % N
        rw [Nat.mod_eq_of_lt (by omega)]
        exact huv
      by_contra hs
      apply hcut
      right
      refine ⟨?_, hpred⟩
      simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hpred]
      exact fun hvu => hs (P.toSetoid.symm hvu)
    · have hsucc : v = u + 1 := by
        apply (sub_eq_iff_eq_add').mp
        apply Fin.ext
        change (v - u).val = 1 % N
        rw [Nat.mod_eq_of_lt (by omega)]
        exact huv
      by_contra hs
      apply hcut
      left
      refine ⟨?_, hsucc⟩
      simpa [cycleBoundaryCuts, hsucc] using hs
  · rintro ⟨hs, huv⟩
    refine ⟨huv, ?_⟩
    rintro (⟨hcut, rfl⟩ | ⟨hcut, rfl⟩)
    · simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and] at hcut
      exact hcut hs
    · simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and] at hcut
      exact hcut (P.toSetoid.symm hs)

/- Taking all actual cyclic block boundaries and then taking the connected components
   of the cut graph recovers the original partition exactly. -/
private theorem connectedCyclePartitionOfCuts_boundaryCuts {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (P : ConnectedCyclePartition N) :
    (connectedCyclePartitionOfCuts (cycleBoundaryCuts P)).toSetoid = P.toSetoid := by
  apply Setoid.ext
  intro u v
  change (cycleGraphWithCuts (cycleBoundaryCuts P)).Reachable u v ↔ P.toSetoid.r u v
  rw [cycleGraphWith_boundaryCuts hN P]
  exact cyclePartitionGraph_reachable_iff P u v

/- The no-cut case is exactly the exceptional partition with one block. -/
theorem cycleBoundaryCuts_eq_empty_iff {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (P : ConnectedCyclePartition N) :
    cycleBoundaryCuts P = ∅ ↔ ∀ u v, P.toSetoid.r u v := by
  constructor
  · intro hcuts u v
    have hgraph : cycleGraphWithCuts (cycleBoundaryCuts P) = SimpleGraph.cycleGraph N := by
      rw [hcuts]
      ext a b
      simp [cycleGraphWithCuts]
    have hreach : (cycleGraphWithCuts (cycleBoundaryCuts P)).Reachable u v := by
      rw [hgraph]
      exact SimpleGraph.cycleGraph_preconnected u v
    rw [cycleGraphWith_boundaryCuts hN P] at hreach
    exact (cyclePartitionGraph_reachable_iff P u v).mp hreach
  · intro hall
    ext u
    simp [cycleBoundaryCuts, hall]

/- An uncut successor edge is an edge of the reconstructed graph, so its endpoints
   belong to the same connected component. -/
private theorem cycleBoundaryCuts_ofCuts_subset {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (cuts : Finset (Fin N)) :
    cycleBoundaryCuts (connectedCyclePartitionOfCuts cuts) ⊆ cuts := by
  intro u hu
  by_contra hnot
  have hadj : (SimpleGraph.cycleGraph N).Adj u (u + 1) := by
    rw [SimpleGraph.cycleGraph_adj']
    right
    simp [Nat.mod_eq_of_lt (show 1 < N by omega)]
  have hsucc : u ≠ (u + 1) + 1 := by
    intro hv
    have ht : (1 : Fin N) + 1 = 0 := by
      apply add_left_cancel (a := u)
      simpa [add_assoc] using hv.symm
    have hval := congrArg Fin.val ht
    norm_num [Fin.add_def, Nat.mod_eq_of_lt (show 2 < N by omega)] at hval
  have hedge : (cycleGraphWithCuts cuts).Adj u (u + 1) := by
    refine ⟨hadj, ?_⟩
    rintro (⟨hcut, _⟩ | ⟨hcut, hback⟩)
    · exact hnot hcut
    · exact hsucc hback
  have hreach : (cycleGraphWithCuts cuts).Reachable u (u + 1) := hedge.reachable
  simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  change ¬ (cycleGraphWithCuts cuts).Reachable u (u + 1) at hu
  exact hu hreach

/- Two deleted successor edges separate the intervening linear arc from its complement.
   The wraparound edge can cross this arc only when its last vertex is the second cut. -/
private theorem cycleGraphWithCuts_arc_invariant {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (cuts : Finset (Fin N)) (a b : Fin N) (_hab : a < b)
    (ha : a ∈ cuts) (hb : b ∈ cuts) (u v : Fin N)
    (hadj : (cycleGraphWithCuts cuts).Adj u v) :
    (a.val < u.val ∧ u.val ≤ b.val) ↔
      (a.val < v.val ∧ v.val ≤ b.val) := by
  have hcrossEdge (x : Fin N) (hx : x ∈ cuts)
      (hforward : u = x ∧ v = x + 1 ∨ v = x ∧ u = x + 1) : False := by
    apply hadj.2
    rcases hforward with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hx, rfl⟩
    · exact Or.inr ⟨hx, rfl⟩
  by_contra hiff
  have hcross :
      ((a.val < u.val ∧ u.val ≤ b.val) ∧
        ¬ (a.val < v.val ∧ v.val ≤ b.val)) ∨
      (¬ (a.val < u.val ∧ u.val ≤ b.val) ∧
        (a.val < v.val ∧ v.val ≤ b.val)) := by tauto
  have hN' : 2 < N := by omega
  rcases cycleGraph_adj_values u v hadj.1 with hstep | hstep | hwrap | hwrap
  · have hboundary : v = a ∨ v = b := by
      rcases hcross with hcross | hcross
      · rcases hcross with ⟨hu, hv⟩
        rcases hu with ⟨hu1, hu2⟩
        by_cases hv1 : a.val < v.val
        · right; apply Fin.ext; omega
        · left; apply Fin.ext; omega
      · rcases hcross with ⟨hu, hv⟩
        rcases hv with ⟨hv1, hv2⟩
        by_cases hu1 : a.val < u.val
        · right; apply Fin.ext; omega
        · left; apply Fin.ext; omega
    have hsucc : u = v + 1 := by
      apply Fin.ext
      have hlt : v.val + 1 < N := by omega
      simpa [Fin.add_def, Nat.mod_eq_of_lt (show 1 < N by omega),
        Nat.mod_eq_of_lt hlt] using hstep
    rcases hboundary with hva | hvb
    · exact hcrossEdge a ha (Or.inr ⟨hva, hva ▸ hsucc⟩)
    · exact hcrossEdge b hb (Or.inr ⟨hvb, hvb ▸ hsucc⟩)
  · have hboundary : u = a ∨ u = b := by
      rcases hcross with hcross | hcross
      · rcases hcross with ⟨hu, hv⟩
        rcases hu with ⟨hu1, hu2⟩
        by_cases hv1 : a.val < v.val
        · right; apply Fin.ext; omega
        · left; apply Fin.ext; omega
      · rcases hcross with ⟨hu, hv⟩
        rcases hv with ⟨hv1, hv2⟩
        by_cases hu1 : a.val < u.val
        · right; apply Fin.ext; omega
        · left; apply Fin.ext; omega
    have hsucc : v = u + 1 := by
      apply Fin.ext
      have hlt : u.val + 1 < N := by omega
      simpa [Fin.add_def, Nat.mod_eq_of_lt (show 1 < N by omega),
        Nat.mod_eq_of_lt hlt] using hstep
    rcases hboundary with hua | hub
    · exact hcrossEdge a ha (Or.inl ⟨hua, hua ▸ hsucc⟩)
    · exact hcrossEdge b hb (Or.inl ⟨hub, hub ▸ hsucc⟩)
  · have hvb : v = b := by
      apply Fin.ext
      rcases hcross with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> omega
    have hsucc : u = v + 1 := by
      apply Fin.ext
      simp only [Fin.add_def, Fin.val_one']
      rcases hwrap with ⟨hu, hv⟩
      simpa [hv, hu, Nat.mod_eq_of_lt (show 1 < N by omega),
        show N - 1 + 1 = N by omega] using hu
    exact hcrossEdge b hb (Or.inr ⟨hvb, hvb ▸ hsucc⟩)
  · have hub : u = b := by
      apply Fin.ext
      rcases hcross with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> omega
    have hsucc : v = u + 1 := by
      apply Fin.ext
      simp only [Fin.add_def, Fin.val_one']
      rcases hwrap with ⟨hv, hu⟩
      simpa [hu, hv, Nat.mod_eq_of_lt (show 1 < N by omega),
        show N - 1 + 1 = N by omega] using hv
    exact hcrossEdge b hb (Or.inl ⟨hub, hub ▸ hsucc⟩)

/- Every block of a connected cycle partition is wholly inside or outside an arc
   bounded by two actual cuts. -/
theorem cyclePartitionBlock_arc_constant {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (P : ConnectedCyclePartition N) (a b : Fin N) (hab : a < b)
    (ha : a ∈ cycleBoundaryCuts P) (hb : b ∈ cycleBoundaryCuts P)
    (u v : Fin N) (huv : P.toSetoid.r u v) :
    (a.val < u.val ∧ u.val ≤ b.val) ↔
      (a.val < v.val ∧ v.val ≤ b.val) := by
  have hreach : (cycleGraphWithCuts (cycleBoundaryCuts P)).Reachable u v := by
    rw [cycleGraphWith_boundaryCuts hN P]
    exact (cyclePartitionGraph_reachable_iff P u v).mpr huv
  obtain ⟨w⟩ := hreach
  induction w with
  | nil => rfl
  | @cons x y z hxy w ih =>
      exact (cycleGraphWithCuts_arc_invariant hN
        (cycleBoundaryCuts P) a b hab ha hb x y hxy).trans
        (ih (by
          apply (cyclePartitionGraph_reachable_iff P y z).mp
          rw [← cycleGraphWith_boundaryCuts hN P]
          exact ⟨w⟩))

/- With two distinct prescribed cuts, the endpoints of either cut lie in different
   components of the actual edge-deleted cycle. -/
private theorem cycleGraphWithCuts_cut_not_reachable {N : ℕ} [NeZero N]
    (hN : 3 ≤ N) (cuts : Finset (Fin N)) (c d : Fin N)
    (hc : c ∈ cuts) (hd : d ∈ cuts) (hcd : c ≠ d) :
    ¬ (cycleGraphWithCuts cuts).Reachable c (c + 1) := by
  intro hreach
  obtain ⟨p⟩ := hreach
  have harc (a b : Fin N) (hab : a < b) (ha : a ∈ cuts) (hb : b ∈ cuts)
      {x y : Fin N} (q : (cycleGraphWithCuts cuts).Walk x y) :
      (a.val < x.val ∧ x.val ≤ b.val) ↔
        (a.val < y.val ∧ y.val ≤ b.val) := by
    induction q with
    | nil => rfl
    | @cons u v w huv _ ih =>
      exact (cycleGraphWithCuts_arc_invariant hN cuts a b hab ha hb u v huv).trans ih
  by_cases hlt : c < d
  · have hcon : c.val < (c + 1).val ∧ (c + 1).val ≤ d.val := by
      have hsmall : c.val + 1 < N := by omega
      have hval : (c + 1).val = c.val + 1 := by
        simp [Fin.add_def, Nat.mod_eq_of_lt (show 1 < N by omega),
          Nat.mod_eq_of_lt hsmall]
      omega
    have hself : ¬ (c.val < c.val ∧ c.val ≤ d.val) := by omega
    exact hself ((harc c d hlt hc hd p).mpr hcon)
  · have hdc : d < c := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hcd)
    have hcon : d.val < c.val ∧ c.val ≤ c.val := by omega
    have hnext : ¬ (d.val < (c + 1).val ∧ (c + 1).val ≤ c.val) := by
      by_cases hsmall : c.val + 1 < N
      · have hval : (c + 1).val = c.val + 1 := by
          simp [Fin.add_def, Nat.mod_eq_of_lt (show 1 < N by omega),
            Nat.mod_eq_of_lt hsmall]
        omega
      · have hlast : c.val + 1 = N := by omega
        have hval : (c + 1).val = 0 := by
          simp [Fin.add_def, Nat.mod_eq_of_lt (show 1 < N by omega), hlast]
        omega
    exact hnext ((harc d c hdc hd hc p).mp hcon)

/- For two or more prescribed cuts, reconstruction has precisely those boundaries.
   Empty and singleton cut sets are outside this theorem's hypothesis. -/
private theorem cycleBoundaryCuts_ofCuts_eq {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (cuts : Finset (Fin N)) (hcuts : 2 ≤ cuts.card) :
    cycleBoundaryCuts (connectedCyclePartitionOfCuts cuts) = cuts := by
  apply Finset.Subset.antisymm (cycleBoundaryCuts_ofCuts_subset hN cuts)
  intro c hc
  obtain ⟨d, hd, hdc⟩ := Finset.exists_mem_ne (by omega : 1 < cuts.card) c
  simp only [cycleBoundaryCuts, Finset.mem_filter, Finset.mem_univ, true_and]
  change ¬ (cycleGraphWithCuts cuts).Reachable c (c + 1)
  exact cycleGraphWithCuts_cut_not_reachable hN cuts c d hc hd (Ne.symm hdc)

/- With no deleted edges, the cycle itself is connected, so there is one block. -/
private theorem cycleBoundaryCuts_noCuts {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    cycleBoundaryCuts (connectedCyclePartitionOfCuts (∅ : Finset (Fin N))) = ∅ := by
  apply (cycleBoundaryCuts_eq_empty_iff hN _).mpr
  intro u v
  change (cycleGraphWithCuts ∅).Reachable u v
  have hgraph : cycleGraphWithCuts (∅ : Finset (Fin N)) = SimpleGraph.cycleGraph N := by
    ext x y
    simp [cycleGraphWithCuts]
  rw [hgraph]
  exact SimpleGraph.cycleGraph_preconnected u v

/- Deleting one cyclic edge leaves the actual cycle connected.  The edge occurs on
   Mathlib's canonical cycle, so it is not a bridge. -/
private theorem cycleBoundaryCuts_singletonCut {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (c : Fin N) :
    cycleBoundaryCuts (connectedCyclePartitionOfCuts ({c} : Finset (Fin N))) = ∅ := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le' hN
  apply (cycleBoundaryCuts_eq_empty_iff hN _).mpr
  intro u v
  change (cycleGraphWithCuts ({c} : Finset (Fin (M + 3)))).Reachable u v
  have hgraph :
      cycleGraphWithCuts ({c} : Finset (Fin (M + 3))) =
        (SimpleGraph.cycleGraph (M + 3)).deleteEdges {s(c, c + 1)} := by
    ext x y
    simp only [cycleGraphWithCuts, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hxy, hcut⟩
      refine ⟨hxy, ?_⟩
      intro hedge
      rcases Sym2.eq_iff.mp hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcut (Or.inl ⟨rfl, rfl⟩)
      · exact hcut (Or.inr ⟨rfl, rfl⟩)
    · rintro ⟨hxy, hedge⟩
      refine ⟨hxy, ?_⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hedge (Sym2.eq_iff.mpr (Or.inl ⟨rfl, rfl⟩))
      · exact hedge (Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩))
  rw [hgraph]
  let p : (SimpleGraph.cycleGraph (M + 3)).Walk (0 : Fin (M + 3)) 0 :=
    SimpleGraph.cycleGraph.cycle M
  have hpCycle : p.IsCycle := SimpleGraph.cycleGraph.isCycle_cycle
  have hpEdge : s(c, c + 1) ∈ p.edges := by
    rw [SimpleGraph.Walk.mk_mem_edges_iff_exists]
    let k := M + 3 - 1 - c.val
    refine ⟨k, ?_, ?_⟩
    · simpa [p, k] using (show M + 3 - 1 - c.val < M + 3 from by omega)
    · have hk : k < M + 3 := by simp [k]; omega
      have hk1 : k + 1 ≤ M + 3 := by omega
      change s((SimpleGraph.cycleGraph.cycle M).getVert k,
        (SimpleGraph.cycleGraph.cycle M).getVert (k + 1)) = s(c, c + 1)
      rw [SimpleGraph.cycleGraph.getVert_cycle (hm := Nat.le_of_lt hk),
        SimpleGraph.cycleGraph.getVert_cycle (hm := hk1)]
      rw [Sym2.eq_iff]
      right
      constructor
      · apply Fin.ext
        dsimp [k]
        by_cases hlast : c.val = M + 2
        · simp [Fin.add_def, hlast]
        · have hc : c.val < M + 2 := by omega
          have hcalc : M + 3 - (M + 2 - c.val) = c.val + 1 := by omega
          rw [hcalc]
          simp [Fin.add_def]
      · apply Fin.ext
        dsimp [k]
        have hcalc : M + 3 - (M + 2 - c.val + 1) = c.val := by omega
        rw [hcalc]
        simp [Nat.mod_eq_of_lt c.isLt]
  have hnotBridge : ¬ (SimpleGraph.cycleGraph (M + 3)).IsBridge s(c, c + 1) := by
    intro hbridge
    exact (SimpleGraph.isBridge_iff_forall_cycle_notMem
      (p.edges_subset_edgeSet hpEdge)).mp hbridge p hpCycle hpEdge
  have hconnected : (SimpleGraph.cycleGraph (M + 3)).Connected := by
    simpa only [Nat.reduceAdd] using (SimpleGraph.cycleGraph_connected (n := M + 2))
  exact (hconnected.connected_delete_edge_of_not_isBridge hnotBridge).preconnected u v

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

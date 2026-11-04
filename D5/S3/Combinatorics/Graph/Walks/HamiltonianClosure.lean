/- GID: D5/S3/Combinatorics/Graph/Walks/HamiltonianClosure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/HamiltonianClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian]
   utility: none
   digest: Endpoint degree sums reroute spanning paths and preserve Hamiltonicity under closure. -/
import D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

/-!
Endpoint neighborhoods of a spanning path force a crossing and an actual Hamilton cycle.

Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0; see docs/reports/licenses/menger-hamiltonian-LICENSE.txt.
Authors: Juan Pablo Traverso Gianini
Adapted from MengerHamilton/ClosureAux.lean and Hamiltonian.lean at
jtraverso/menger-hamiltonian@35c5f684f9bfbd244bd0999ce725623ab571adb6.
The receiver uses native walks and existing cycle slicing and splicing.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure

open SimpleGraph
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

/-- A spanning path closes after rerouting when its endpoint degrees sum to
at least the number of vertices, provided that number is at least three. -/
theorem exists_hamiltonian_cycle_of_path {a b : V} (p : G.Walk a b)
    (hp : p.IsHamiltonian) (hn : 3 ≤ Fintype.card V)
    (hdeg : Fintype.card V ≤ G.degree a + G.degree b) :
    ∃ c : G.Walk a a, c.IsHamiltonianCycle := by
  classical
  set n := Fintype.card V with hn_def
  let x := p.getVert
  have hlen : p.length = n - 1 := hp.length_eq
  have hslen : p.support.length = n := hp.length_support
  have hx0 : x 0 = a := p.getVert_zero
  have hxn : x (n - 1) = b := by rw [← hlen]; exact p.getVert_length
  have hinj : ∀ i j, i < n → j < n → x i = x j → i = j := by
    intro i j hi hj hij
    have he : hp.getVertEquiv ⟨i, by omega⟩ = hp.getVertEquiv ⟨j, by omega⟩ := hij
    exact congrArg Fin.val (hp.getVertEquiv.injective he)
  have hsurj : ∀ w, ∃ j < n, x j = w := by
    intro w
    obtain ⟨j, hj⟩ := hp.getVertEquiv.surjective w
    exact ⟨j.val, by have := j.isLt; omega, hj⟩
  have hdeg : n ≤ G.degree (x 0) + G.degree (x (n - 1)) := by
    rw [hx0, hxn]
    exact hdeg
  set I := (Finset.range (n - 1)).filter (fun i => G.Adj (x 0) (x (i + 1))) with hI_def
  set J := (Finset.range (n - 1)).filter (fun i => G.Adj (x (n - 1)) (x i)) with hJ_def
  have hI : I.card = G.degree (x 0) := by
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset (x 0) = I.image (fun i => x (i + 1)) := by
      ext w
      simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range, I]
      constructor
      · intro hw
        obtain ⟨j, hj, rfl⟩ := hsurj w
        have hj0 : j ≠ 0 := by rintro rfl; exact G.irrefl hw
        refine ⟨j - 1, ⟨by omega, ?_⟩, ?_⟩
        · rwa [Nat.sub_add_cancel (by omega)]
        · rw [Nat.sub_add_cancel (by omega)]
      · rintro ⟨i, ⟨_, hi⟩, rfl⟩
        exact hi
    rw [this, Finset.card_image_of_injOn]
    intro i hi j hj hij
    have hi' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1
    have hj' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
    have := hinj _ _ (by omega) (by omega) hij
    omega
  have hJ : J.card = G.degree (x (n - 1)) := by
    rw [← card_neighborFinset_eq_degree]
    have : G.neighborFinset (x (n - 1)) = J.image x := by
      ext w
      simp only [mem_neighborFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_range, J]
      constructor
      · intro hw
        obtain ⟨j, hj, rfl⟩ := hsurj w
        have hj0 : j ≠ n - 1 := by rintro rfl; exact G.irrefl hw
        exact ⟨j, ⟨by omega, hw⟩, rfl⟩
      · rintro ⟨i, ⟨_, hi⟩, rfl⟩
        exact hi
    rw [this, Finset.card_image_of_injOn]
    intro i hi j hj hij
    have hi' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1
    have hj' := Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).1
    exact hinj _ _ (by omega) (by omega) hij
  have hex : ∃ i, i < n - 1 ∧ G.Adj (x 0) (x (i + 1)) ∧ G.Adj (x (n - 1)) (x i) := by
    by_contra hne
    push Not at hne
    have hdisj : Disjoint I J := by
      rw [Finset.disjoint_left]
      intro i hiI hiJ
      simp only [I, J, Finset.mem_filter, Finset.mem_range] at hiI hiJ
      exact hne i hiI.1 hiI.2 hiJ.2
    have h1 := Finset.card_union_of_disjoint hdisj
    have hsub : I ∪ J ⊆ Finset.range (n - 1) :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_range] at h2
    omega
  obtain ⟨i, hi, hu, hv⟩ := hex
  let first : Piece G := ⟨a, x i, p.take i⟩
  let last : Piece G := ⟨b, x (i + 1), (p.drop (i + 1)).reverse⟩
  have hfull : ∀ w : V,
      ((first :: [last]).flatMap fun z => z.walk.support).count w = 1 := by
    intro w
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change ((p.take i).support ++ (p.drop (i + 1)).reverse.support).count w = 1
    rw [Walk.support_reverse, List.count_append, List.count_reverse,
      Walk.support_take, Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left (by omega)]
    rw [← List.count_append, List.take_append_drop]
    exact hp w
  have hsize : 3 ≤ ((first :: [last]).flatMap fun z => z.walk.support).length := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change 3 ≤ ((p.take i).support ++ (p.drop (i + 1)).reverse.support).length
    rw [Walk.support_reverse, List.length_append, List.length_reverse,
      Walk.support_take, Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left (by omega), List.length_take, List.length_drop]
    omega
  obtain ⟨c, hc, _, _⟩ := exists_spliced_hamiltonian_cycle first [last]
    (by exact ⟨by simpa only [first, last, hxn] using hv.symm, trivial⟩)
    (by simpa only [finish, first, last, hx0] using hu.symm) hfull hsize
  exact ⟨c, hc⟩


/-- Bondy--Chvatal: adding an absent edge with endpoint degree sum at least
cardinality preserves Hamiltonicity. The degrees belong to the original graph. -/
theorem isHamiltonian_sup_edge_iff {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hdeg : Fintype.card V ≤ G.degree u + G.degree v) :
    (G ⊔ edge u v).IsHamiltonian ↔ G.IsHamiltonian := by
  classical
  have hbound : ∀ x y : V, x ≠ y → ¬ G.Adj x y →
      G.degree x + 2 ≤ Fintype.card V := by
    intro x y hxy hnon
    rw [← card_neighborFinset_eq_degree]
    have hx : x ∉ insert y (G.neighborFinset x) := by simp [hxy]
    have hy : y ∉ G.neighborFinset x := by simpa using hnon
    have h := Finset.card_le_univ (insert x (insert y (G.neighborFinset x)))
    rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hy] at h
    omega
  have hdu := hbound u v huv hnadj
  have hdv := hbound v u huv.symm (by simpa [G.adj_comm] using hnadj)
  have hn : 3 ≤ Fintype.card V := by omega
  constructor
  · intro hH
    obtain ⟨a, p, hp⟩ := hH (by omega)
    by_cases he : s(u, v) ∈ p.edgeSet
    · obtain ⟨q, hq, hqEdges⟩ := exists_open_cycle_at_edge p hp he
      have htransfer : ∀ e, e ∈ q.edges → e ∈ G.edgeSet := by
        intro e heq
        obtain ⟨hep, hne⟩ := (hqEdges e).mp heq
        have hmem := p.edges_subset_edgeSet hep
        rw [edgeSet_sup] at hmem
        rcases hmem with hmem | hmem
        · exact hmem
        · simp only [edgeSet_edge_of_ne huv, Set.mem_singleton_iff] at hmem
          exact (hne hmem).elim
      let r := q.transfer G htransfer
      have hr : r.IsHamiltonian := (Walk.isHamiltonian_transfer htransfer).mpr hq
      obtain ⟨c, hc⟩ := exists_hamiltonian_cycle_of_path G r hr hn (by omega)
      exact hc.isHamiltonian
    · have htransfer : ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
        intro e hep
        have hmem := p.edges_subset_edgeSet hep
        rw [edgeSet_sup] at hmem
        rcases hmem with hmem | hmem
        · exact hmem
        · simp only [edgeSet_edge_of_ne huv, Set.mem_singleton_iff] at hmem
          exact (he (hmem ▸ hep)).elim
      exact ((Walk.isHamiltonianCycle_transfer htransfer).mpr hp).isHamiltonian
  · intro h
    exact h.mono le_sup_left

/-- Ore: at least three vertices and the degree-sum condition on every distinct
nonadjacent pair imply Hamiltonicity, without a connectedness assumption. -/
theorem ore (hn : 3 ≤ Fintype.card V)
    (hdeg : ∀ u v, u ≠ v → ¬ G.Adj u v → Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  suffices key : ∀ N (H : SimpleGraph V) [DecidableRel H.Adj],
      (Finset.univ.filter (fun p : V × V => p.1 ≠ p.2 ∧ ¬ H.Adj p.1 p.2)).card = N →
      (∀ u v, u ≠ v → ¬ H.Adj u v → Fintype.card V ≤ H.degree u + H.degree v) →
      H.IsHamiltonian from key _ G rfl hdeg
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro H _ hN hH
    by_cases hall : ∀ u v, u ≠ v → H.Adj u v
    · have htop : H = ⊤ := by
        ext u v
        exact ⟨fun h => h.ne, hall u v⟩
      rw [htop]
      exact isHamiltonian_top hn
    push Not at hall
    obtain ⟨u, v, huv, hnadj⟩ := hall
    classical
    have hle : H ≤ H ⊔ edge u v := le_sup_left
    rw [← isHamiltonian_sup_edge_iff H huv hnadj (hH u v huv hnadj)]
    refine ih _ ?_ (H ⊔ edge u v) rfl ?_
    · rw [← hN]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨(u, v), ?_, ?_⟩
        · simp [huv, hnadj]
        · simp [huv, edge_adj]
      · intro p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => h2 (hle h)⟩
    · intro a b hab hnab
      have h := hH a b hab (fun h => hnab (hle h))
      exact h.trans (add_le_add (degree_le_of_le hle) (degree_le_of_le hle))

#print axioms exists_hamiltonian_cycle_of_path
#print axioms isHamiltonian_sup_edge_iff
#print axioms ore

end D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure

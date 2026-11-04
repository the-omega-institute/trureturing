/- GID: D5/S3/Combinatorics/Graph/Walks/HamiltonianClosure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/HamiltonianClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [library/GraphInvariants/traversogianini2026brooks]
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

end D5.S3.Combinatorics.Graph.Walks.HamiltonianClosure

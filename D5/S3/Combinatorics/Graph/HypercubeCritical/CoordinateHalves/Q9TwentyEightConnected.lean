import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourExpansion

/-! Connectedness of the 28-point side of a coordinate cut. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyEightConnected

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open GirthSliceCounting (degreeTwo degreeThree cubic_slice_counting)
open TwoBalancedComponents (componentFinset)
open private paritySide parity_bipartite parity_union parts_card sum_degrees_parts
  twice_low_le_three_high coordinate_slice_degree_cases coordinate_slice_low_independent
  balanced_subset from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private componentFinset_nonempty componentFinset_subset componentFinset_neighbor_closed
  componentFinset_disjoint induced_degree_eq_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
open private suppress from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression
open private High vertex vertex_degree vertex_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourExpansion
open private compressed from D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem small_profile_impossible (a b p r : Fin 15) :
    0 < a.val + b.val + p.val + r.val →
    a.val + b.val + p.val + r.val ≤ 14 →
    3 * a.val + 2 * p.val = 3 * b.val + 2 * r.val →
    2 * (p.val + r.val) ≤ 3 * (a.val + b.val) →
    15 * a.val ≤ a.val * (b.val + r.val) + 2 * b.val + 4 * r.val →
    15 * b.val ≤ b.val * (a.val + p.val) + 2 * a.val + 4 * p.val → False := by
  revert a b p r
  decide +kernel

attribute [local instance] Classical.propDecidable

private theorem fifteen_le_card {S : Finset (Q 9)} (hS : S.Nonempty) (hb : IsBalanced S)
    (hdeg : ∀ x : (S : Set (Q 9)),
      ((hypercube 9).induce (S : Set (Q 9))).degree x = 2 ∨
      ((hypercube 9).induce (S : Set (Q 9))).degree x = 3)
    (hlow : ∀ {x y : (S : Set (Q 9))}, (hypercube 9).Adj x.val y.val →
      ((hypercube 9).induce (S : Set (Q 9))).degree x = 2 →
      ((hypercube 9).induce (S : Set (Q 9))).degree y = 2 → False) :
    15 ≤ S.card := by
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S false
  let R := paritySide S true
  let a := (degreeThree G L).card
  let b := (degreeThree G R).card
  let p := (degreeTwo G L).card
  let r := (degreeTwo G R).card
  have hp : G.IsBipartiteWith (L : Set _) (R : Set _) := parity_bipartite S
  have hu : L ∪ R = univ := parity_union S
  have hd : Disjoint L R := Finset.disjoint_coe.mp hp.disjoint
  have hcards : L.card + R.card = S.card := by
    rw [← card_union_of_disjoint hd, hu, card_univ]
    exact Fintype.card_coe S
  have hpartsL : p + a = L.card := parts_card G hdeg L
  have hpartsR : r + b = R.card := parts_card G hdeg R
  have htotal : a + b + p + r = S.card := by omega
  have hbalance : 2 * p + 3 * a = 2 * r + 3 * b :=
    (sum_degrees_parts G hdeg L).symm.trans
      ((SimpleGraph.isBipartiteWith_sum_degrees_eq hp).trans (sum_degrees_parts G hdeg R))
  have hcounts := twice_low_le_three_high G hdeg (fun hxy hx hy => hlow hxy hx hy)
  have hlowCount : (degreeTwo G univ).card = p + r := by
    have hdisj : Disjoint (degreeTwo G L) (degreeTwo G R) :=
      hd.mono (filter_subset _ _) (filter_subset _ _)
    have he : degreeTwo G L ∪ degreeTwo G R = degreeTwo G univ := by
      simp only [degreeTwo, ← filter_union, hu]
    exact (congrArg card he).symm.trans (card_union_of_disjoint hdisj)
  have hhighCount : (degreeThree G univ).card = a + b := by
    have hdisj : Disjoint (degreeThree G L) (degreeThree G R) :=
      hd.mono (filter_subset _ _) (filter_subset _ _)
    have he : degreeThree G L ∪ degreeThree G R = degreeThree G univ := by
      simp only [degreeThree, ← filter_union, hu]
    exact (congrArg card he).symm.trans (card_union_of_disjoint hdisj)
  rw [hlowCount, hhighCount] at hcounts
  have hpaths := cubic_slice_counting hp hdeg (fun hxy hx hy => hlow hxy hx hy)
    (BalancedCubeGirth.eight_le_egirth S hb)
  change 15 * a ≤ a * R.card + 2 * b + 4 * r ∧
    15 * b ≤ b * L.card + 2 * a + 4 * p at hpaths
  rw [← hpartsL, ← hpartsR, Nat.add_comm r b, Nat.add_comm p a] at hpaths
  by_contra! hs
  have hn := card_pos.mpr hS
  have hpositive : 0 < a + b + p + r := by omega
  have hsmall : a + b + p + r ≤ 14 := by omega
  have hbalanced : 3 * a + 2 * p = 3 * b + 2 * r := by omega
  exact small_profile_impossible ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨p, by omega⟩ ⟨r, by omega⟩
    hpositive hsmall hbalanced hcounts hpaths.1 hpaths.2

/-- Every 28-point half of a balanced induced cubic subgraph of the nine-cube
is connected. -/
theorem half_connected {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 28) :
    ((hypercube 9).induce (coordinateSlice C b : Set (Q 9))).Connected := by
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  have hScard : S.card = 28 := hs
  have hsize (K : G.ConnectedComponent) : 15 ≤ (componentFinset S K).card := by
    let T := componentFinset S K
    let J := (hypercube 9).induce (T : Set (Q 9))
    let point (x : (T : Set (Q 9))) : (S : Set (Q 9)) :=
      ⟨x.val, componentFinset_subset S K x.property⟩
    have hdegree (x : (T : Set (Q 9))) : J.degree x = G.degree (point x) := by
      change ((hypercube 9).induce (T : Set (Q 9))).degree x =
        ((hypercube 9).induce (S : Set (Q 9))).degree (point x)
      rw [induced_degree_eq_neighbor_card T x, induced_degree_eq_neighbor_card S (point x)]
      congr 1
      ext y
      simp only [mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨fun ⟨hxy, hy⟩ => ⟨hxy, componentFinset_subset S K hy⟩,
        fun ⟨hxy, hy⟩ => ⟨hxy, componentFinset_neighbor_closed S K x.val x.property y hy hxy⟩⟩
    have hT := componentFinset_subset S K
    exact fifteen_le_card (componentFinset_nonempty S K)
      (balanced_subset hb (hT.trans (filter_subset _ _)))
      (fun x => by rw [hdegree x]; exact coordinate_slice_degree_cases (point x).property hr)
      (fun {x y} hxy hx hy => coordinate_slice_low_independent hr hb
        (x := point x) (y := point y) hxy (by rw [← hdegree x]; exact hx)
        (by rw [← hdegree y]; exact hy))
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < S.card by omega)
  refine G.connected_iff_exists_forall_reachable.mpr ⟨⟨x, hx⟩, fun y => ?_⟩
  by_contra hn
  let K := G.connectedComponentMk ⟨x, hx⟩
  let L := G.connectedComponentMk y
  have hd := componentFinset_disjoint S K L (fun he => hn (ConnectedComponent.exact he))
  have hle := card_le_card (union_subset (componentFinset_subset S K) (componentFinset_subset S L))
  rw [card_union_of_disjoint hd, hScard] at hle
  have hk := hsize K
  have hl := hsize L
  omega

#print axioms half_connected

private theorem suppress_connected {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {L R : Finset V} (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hcover : L ∪ R = univ) (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hc : G.Connected) : (suppress G L R).Connected := by
  classical
  let J := suppress G L R
  have hd : Disjoint L R := Finset.disjoint_coe.mp hp.disjoint
  have label (v : V) (hv : G.degree v = 3) : ∃ x : High G L R, vertex x = v := by
    have hm : v ∈ L ∪ R := hcover.symm ▸ mem_univ v
    rcases mem_union.mp hm with hl | hr
    · exact ⟨.inl ⟨v, mem_filter.mpr ⟨hl, hv⟩⟩, rfl⟩
    · exact ⟨.inr ⟨v, mem_filter.mpr ⟨hr, hv⟩⟩, rfl⟩
  have pick (v : V) : ∃ x : High G L R, (G.degree v = 3 ∧ vertex x = v) ∨
      (G.degree v = 2 ∧ G.Adj v (vertex x)) := by
    rcases hdeg v with hv | hv
    · have hcard : (G.neighborFinset v).card = 2 := (G.card_neighborFinset_eq_degree v).trans hv
      obtain ⟨w, hw⟩ := card_pos.mp (show 0 < (G.neighborFinset v).card by rw [hcard]; decide)
      have hvw := (G.mem_neighborFinset v w).mp hw
      rcases hdeg w with hw | hw
      · exact (hlow hvw hv hw).elim
      · obtain ⟨x, rfl⟩ := label w hw
        exact ⟨x, Or.inr ⟨hv, hvw⟩⟩
    · obtain ⟨x, hx⟩ := label v hv
      exact ⟨x, Or.inl ⟨hv, hx⟩⟩
  choose f hf using pick
  have hhigh (x : High G L R) : f (vertex x) = x := by
    rcases hf (vertex x) with h | h
    · exact vertex_injective hd h.2
    · have hx := vertex_degree x
      omega
  have direct (x y : High G L R) (hxy : G.Adj (vertex x) (vertex y)) : J.Adj x y := by
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact (Finset.disjoint_left.mp hd (mem_filter.mp y.property).1
          (hp.mem_of_mem_adj (mem_filter.mp x.property).1 hxy)).elim
      | inr y => exact hxy
    | inr x =>
      cases y with
      | inl y => exact hxy
      | inr y =>
        exact (Finset.disjoint_left.mp hd
          (hp.mem_of_mem_adj' (mem_filter.mp x.property).1 hxy.symm)
          (mem_filter.mp y.property).1).elim
  have through (x y : High G L R) {m : V} (hm : G.degree m = 2)
      (hxm : G.Adj (vertex x) m) (hym : G.Adj (vertex y) m) : J.Reachable x y := by
    by_cases h : x = y
    · subst y
      exact Reachable.rfl
    apply Adj.reachable
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact (show (compressed G L).Adj x y from
          ⟨fun he => h (congrArg Sum.inl he), m, hm, hxm, hym⟩)
      | inr y =>
        exact (Finset.disjoint_left.mp hd
          (hp.mem_of_mem_adj' (mem_filter.mp y.property).1 hym.symm)
          (hp.mem_of_mem_adj (mem_filter.mp x.property).1 hxm)).elim
    | inr x =>
      cases y with
      | inl y =>
        exact (Finset.disjoint_left.mp hd
          (hp.mem_of_mem_adj' (mem_filter.mp x.property).1 hxm.symm)
          (hp.mem_of_mem_adj (mem_filter.mp y.property).1 hym)).elim
      | inr y =>
        exact (show (compressed G R).Adj x y from
          ⟨fun he => h (congrArg Sum.inr he), m, hm, hxm, hym⟩)
  have route {u v : V} (huv : G.Adj u v) : J.Reachable (f u) (f v) := by
    rcases hf u with ⟨_, hu⟩ | ⟨hu, huf⟩ <;> rcases hf v with ⟨_, hv⟩ | ⟨hv, hvf⟩
    · exact (direct _ _ (hu.symm ▸ hv.symm ▸ huv)).reachable
    · exact through _ _ hv (hu.symm ▸ huv) hvf.symm
    · exact through _ _ hu huf.symm (hv.symm ▸ huv.symm)
    · exact (hlow huv hu hv).elim
  have lift {u v : V} (h : G.Reachable u v) : J.Reachable (f u) (f v) := by
    obtain ⟨w⟩ := h
    induction w with
    | nil => exact Reachable.rfl
    | cons h _ ih => exact (route h).trans ih
  obtain ⟨root, hroot⟩ := G.connected_iff_exists_forall_reachable.mp hc
  exact J.connected_iff_exists_forall_reachable.mpr
    ⟨f root, fun x => hhigh x ▸ lift (hroot (vertex x))⟩

/-- Suppressing the degree-two vertices of a 28-point half preserves its connectedness. -/
theorem suppressed_half_connected {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 28) :
    let S := coordinateSlice C b
    let G := (hypercube 9).induce (S : Set (Q 9))
    (suppress G (paritySide S false) (paritySide S true)).Connected := by
  exact suppress_connected (parity_bipartite _) (parity_union _)
    (fun x => coordinate_slice_degree_cases x.property hr)
    (fun hxy hx hy => coordinate_slice_low_independent hr hb hxy hx hy) (half_connected hr hb b hs)

#print axioms suppressed_half_connected

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyEightConnected

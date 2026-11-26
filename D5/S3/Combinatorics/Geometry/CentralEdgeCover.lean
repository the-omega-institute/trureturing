/- GID: D5/S3/Combinatorics/Geometry/CentralEdgeCover
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/CentralEdgeCover
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: An n-point metric space with k central values has at least (k-1)⌈n/2⌉ central edges. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#318)
escape_witness: lengthEdges_card (each nonzero central length class covers every point, hence
  has at least ⌈n/2⌉ edges)
proof_shape:
  len, lengthEdges: definitions; consumers: lengthEdges_card, edge_cover_bound,
    UltrametricThreeCentralMinimum.
  lengthEdges_card: content; consumers: edge_cover_bound, UltrametricThreeCentralMinimum.
  edge_cover_bound: content via lengthEdges_card.
Direct frozen dependency: D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges
  (center, centralGraph).
-/

import D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges

/-! # Edge-cover lower bound for central graphs

For a finite metric space with `n` points whose set of central distances has `k` elements,
the central graph has at least `(k - 1) ⌈n / 2⌉` edges: for each nonzero central value `t`,
the edges of length `t` cover every point, so there are at least `⌈n / 2⌉` of them, and edges of
different lengths are distinct.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Geometry.CentralEdgeCover

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges

noncomputable section

/-- The length of an unordered pair. -/
def len {X : Type} [MetricSpace X] : Sym2 X → ℝ :=
  Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩

open Classical in
/-- The central edges of length `t`. -/
def lengthEdges (X : Type) [Fintype X] [MetricSpace X] (t : ℝ) : Finset (Sym2 X) :=
  (centralGraph X).edgeFinset.filter fun e => len e = t

open Classical in
/-- A nonzero central value has at least `⌈n / 2⌉` central edges of that length. -/
lemma lengthEdges_card (X : Type) [Fintype X] [MetricSpace X] {t : ℝ}
    (ht : t ∈ center X) (ht0 : t ≠ 0) :
    (Fintype.card X + 1) / 2 ≤ (lengthEdges X t).card := by
  have hy : ∀ x : X, ∃ y : X, dist y x = t := ht.2
  choose f hf using hy
  let g : X → Sym2 X := fun x => s(x, f x)
  have hg : ∀ x ∈ (Finset.univ : Finset X), g x ∈ lengthEdges X t := by
    intro x _
    have hne : x ≠ f x := by
      intro h
      have := hf x
      rw [← h, dist_self] at this
      exact ht0 this.symm
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      simp only [centralGraph, SimpleGraph.fromRel_adj]
      refine ⟨hne, Or.inr ?_⟩
      rw [hf x]
      exact ht
    · simp only [g, len, Sym2.lift_mk]
      rw [dist_comm]
      exact hf x
  have hfib : ∀ e ∈ lengthEdges X t,
      ((Finset.univ : Finset X).filter fun x => g x = e).card ≤ 2 := by
    intro e _
    induction e using Sym2.ind with
    | h a b =>
      calc ((Finset.univ : Finset X).filter fun x => g x = s(a, b)).card
          ≤ ({a, b} : Finset X).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, g] at hx
            have hmem : x ∈ s(a, b) := by rw [← hx]; exact Sym2.mem_mk_left x (f x)
            rcases Sym2.mem_iff.mp hmem with h | h <;> simp [h]
        _ ≤ 2 := Finset.card_le_two
  have := Finset.card_le_mul_card_image_of_maps_to hg 2 hfib
  rw [Finset.card_univ] at this
  omega

open Classical in
/-- For a finite metric space with `n` points and `k` central values (zero included), the
central graph has at least `(k - 1) ⌈n / 2⌉` edges. -/
theorem edge_cover_bound (X : Type) [Fintype X] [MetricSpace X] :
    (Nat.card (center X) - 1) * ((Fintype.card X + 1) / 2) ≤
      (centralGraph X).edgeFinset.card := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨p⟩⟩
  · simp [Fintype.card_eq_zero]
  · let D : Finset ℝ := (Finset.univ : Finset (X × X)).image fun q => dist q.1 q.2
    let Cf : Finset ℝ := D.filter fun t => t ∈ center X
    have hC : center X = ↑Cf := by
      ext t
      simp only [Cf, D, Finset.coe_filter, Finset.mem_image, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq]
      constructor
      · intro ht
        obtain ⟨y, hy⟩ := ht.2 p
        exact ⟨⟨(y, p), hy⟩, ht⟩
      · exact fun h => h.2
    have hk : Nat.card (center X) = Cf.card := by
      rw [hC, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have h0 : (0 : ℝ) ∈ Cf := by
      have : (0 : ℝ) ∈ center X := ⟨le_rfl, fun x => ⟨x, dist_self x⟩⟩
      rw [hC] at this
      exact this
    have hdisj : Set.PairwiseDisjoint (↑(Cf.erase 0) : Set ℝ) (lengthEdges X) := by
      intro s _ t _ hst
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e hs ht
      simp only [lengthEdges, Finset.mem_filter] at hs ht
      exact hst (hs.2.symm.trans ht.2)
    have hsub : (Cf.erase 0).biUnion (lengthEdges X) ⊆ (centralGraph X).edgeFinset := by
      intro e he
      obtain ⟨t, _, het⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_filter.mp het).1
    have hsum : ∑ t ∈ Cf.erase 0, (lengthEdges X t).card ≤ (centralGraph X).edgeFinset.card := by
      rw [← Finset.card_biUnion hdisj]
      exact Finset.card_le_card hsub
    have hlow : (Cf.erase 0).card * ((Fintype.card X + 1) / 2) ≤
        ∑ t ∈ Cf.erase 0, (lengthEdges X t).card := by
      have := Finset.card_nsmul_le_sum (Cf.erase 0) (fun t => (lengthEdges X t).card)
        ((Fintype.card X + 1) / 2) (fun t ht => by
          have ht0 := Finset.ne_of_mem_erase ht
          have htC : t ∈ center X := by
            rw [hC]
            exact Finset.mem_of_mem_erase ht
          exact lengthEdges_card X htC ht0)
      rwa [smul_eq_mul] at this
    rw [hk, ← Finset.card_erase_of_mem h0]
    exact hlow.trans hsum

end

end D5.S3.Combinatorics.Geometry.CentralEdgeCover

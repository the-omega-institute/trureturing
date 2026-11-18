import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneThetaGeometryProbe

/-! The two-high side of a balanced 21-point slice fixes four separated ends. -/

set_option autoImplicit false
noncomputable section

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
open GirthSliceCounting (degreeTwo degreeThree)
open private SideHigh compressed compressed_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private one_three_cross_impossible three_walk_endpoint_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private side_high_neighbors_card high_neighbors_compressed_separated from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta
open private twenty_one_slice_compression from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneCompressionProbe
open private four_high_slice_impossible from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9TwentyOneThetaGeometryProbe
open private paritySide parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
attribute [local instance] Classical.propDecidable

private lemma twenty_one_slice_remaining_case
    (S : Finset (Q 9)) (hS : S.card = 21) (hb : IsBalanced S)
    (hdeg : ∀ v, ((hypercube 9).induce (S : Set (Q 9))).degree v = 2 ∨
      ((hypercube 9).induce (S : Set (Q 9))).degree v = 3)
    (hcount : (degreeTwo ((hypercube 9).induce (S : Set (Q 9))) univ).card = 11)
    (hlow : ∀ ⦃v w⦄, ((hypercube 9).induce (S : Set (Q 9))).Adj v w →
      ((hypercube 9).induce (S : Set (Q 9))).degree v = 2 →
      ((hypercube 9).induce (S : Set (Q 9))).degree w = 2 → False) :
    ∃ b : Bool,
      let G := (hypercube 9).induce (S : Set (Q 9))
      let L := paritySide S b
      let R := paritySide S (!b)
      Fintype.card (SideHigh G L) = 2 ∧ Fintype.card (SideHigh G R) = 8 ∧
        (compressed G L).edgeFinset.card = 1 ∧ (compressed G R).edgeFinset.card = 10 := by
  obtain ⟨b, hcases⟩ := twenty_one_slice_compression S hS hb hdeg hcount hlow
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S b
  let R := paritySide S (!b)
  have hp : G.IsBipartiteWith (L : Set (S : Set (Q 9))) (R : Set (S : Set (Q 9))) := by
    cases b
    · exact parity_bipartite S
    · exact (parity_bipartite S).symm
  rcases hcases with h | ⟨⟨e⟩, hR, _, hcross⟩
  · exact ⟨b, h⟩
  · exact (four_high_slice_impossible hb hp hdeg (fun hxy hx hy => hlow hxy hx hy)
      e hcross hR).elim

/-- The two roots have two opposite high neighbors each. The four opposite
ends are independent in the compression, and the two ends from either root
have no common compressed neighbor. -/
private lemma two_high_end_sets
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {L R : Finset V}
    (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : Fintype.card (SideHigh G L) = 2)
    (he : (compressed G L).edgeFinset.card = 1) :
    ∃ x y : SideHigh G L, (compressed G L).Adj x y ∧
      let A (r : SideHigh G L) := (univ : Finset (SideHigh G R)).filter
        (fun u => G.Adj r.val u.val)
      (A x).card = 2 ∧ (A y).card = 2 ∧ Disjoint (A x) (A y) ∧
      (∀ u ∈ A x ∪ A y, ∀ v ∈ A x ∪ A y, ¬ (compressed G R).Adj u v) ∧
      ∀ r ∈ ({x, y} : Finset (SideHigh G L)), ∀ u ∈ A r, ∀ v ∈ A r, u ≠ v →
        ∀ w, (compressed G R).Adj u w → (compressed G R).Adj v w → False := by
  let H := compressed G L
  let K := compressed G R
  let A (r : SideHigh G L) := (univ : Finset (SideHigh G R)).filter (fun u => G.Adj r.val u.val)
  have hn : H.edgeFinset.Nonempty := card_pos.mp (by change 0 < (compressed G L).edgeFinset.card; omega)
  obtain ⟨x, y, hxy⟩ := ne_bot_iff_exists_adj.mp (H.edgeFinset_nonempty.mp hn)
  obtain ⟨hxyn, a, ha, hxa, hya⟩ := hxy
  have high (r : SideHigh G L) : G.degree r.val = 3 := (mem_filter.mp r.property).2
  have rightHigh (r : SideHigh G R) : G.degree r.val = 3 := (mem_filter.mp r.property).2
  have left (r : SideHigh G L) : r.val ∈ L := (mem_filter.mp r.property).1
  have two (r t : SideHigh G L) (hrt : H.Adj r t) : (A r).card = 2 := by
    have lo := (H.degree_pos_iff_exists_adj r).2 ⟨t, hrt⟩
    have hi := H.degree_lt_card_verts r
    rw [hL] at hi
    have hr1 : H.degree r = 1 := by omega
    have hd := compressed_degree hp hdeg hlow hg r
    change H.degree r + (degreeThree G (G.neighborFinset r.val)).card = 3 at hd
    rw [hr1] at hd
    change ((univ : Finset (SideHigh G R)).filter (fun u => G.Adj r.val u.val)).card = 2
    rw [side_high_neighbors_card hp (left r)]
    exact Nat.add_left_cancel hd
  have edge {r : SideHigh G L} {u : SideHigh G R} (hu : u ∈ A r) : G.Adj r.val u.val :=
    (mem_filter.mp hu).2
  have hxy' : x.val ≠ y.val := fun h => hxyn (Subtype.ext h)
  have hdis : Disjoint (A x) (A y) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have hau : a ≠ u.val := fun h => by rw [h, rightHigh] at ha; omega
    exact one_three_cross_impossible hp hg (left x) (left x)
      (edge hu) hxa hya.symm (edge hv) hxy' hau ⟨rfl, rfl⟩
  have same (r : SideHigh G L) (u v : SideHigh G R) (hu : u ∈ A r) (hv : v ∈ A r)
      (hne : u ≠ v) := high_neighbors_compressed_separated hp hg (left r) (high r)
        (edge hu) (edge hv) hne
  have cross (u v : SideHigh G R) (hu : u ∈ A x) (hv : v ∈ A y) : ¬ K.Adj u v := by
    rintro ⟨huv, b, hb, hub, hvb⟩
    have hav : a ≠ v.val := fun h => by rw [h, rightHigh] at ha; omega
    have hxb : x.val ≠ b := fun h => by rw [← h, high] at hb; omega
    have huv' : u.val ≠ v.val := fun h => huv (Subtype.ext h)
    have ht := three_walk_endpoint_injective hp hg (left x) (left x)
      hxa hya.symm (edge hv) (edge hu) hub hvb.symm hxy' hav hxb huv' ⟨rfl, rfl⟩
    rw [ht.2.1, rightHigh] at ha
    omega
  have hxy : H.Adj x y := ⟨hxyn, a, ha, hxa, hya⟩
  refine ⟨x, y, hxy, two x y hxy, two y x hxy.symm, hdis, ?_, ?_⟩
  · intro u hu v hv he'
    rcases mem_union.mp hu with hu | hu <;> rcases mem_union.mp hv with hv | hv
    · exact (same x u v hu hv he'.ne).1 he'
    · exact cross u v hu hv he'
    · exact cross v u hv hu he'.symm
    · exact (same y u v hu hv he'.ne).1 he'
  · intro r _ u hu v hv hne
    exact (same r u v hu hv hne).2

#print axioms twenty_one_slice_remaining_case
#print axioms two_high_end_sets

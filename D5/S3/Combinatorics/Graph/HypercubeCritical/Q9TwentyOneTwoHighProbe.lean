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

/-- Each of the four remaining vertices has a unique neighbor in either pair
of separated ends, and a unique neighbor among the remaining vertices. -/
private lemma separated_pairs_core
    {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
    (U W : Finset V) (hcard : Fintype.card V = 8)
    (hU : U.card = 2) (hW : W.card = 2) (hdis : Disjoint U W)
    (hind : ∀ u ∈ U ∪ W, ∀ v ∈ U ∪ W, ¬ K.Adj u v)
    (hsepU : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ∀ z, K.Adj u z → K.Adj v z → False)
    (hsepW : ∀ u ∈ W, ∀ v ∈ W, u ≠ v → ∀ z, K.Adj u z → K.Adj v z → False)
    (hdeg : ∀ x, K.degree x = if x ∈ U ∪ W then 2 else 3) :
    let C := (univ : Finset V) \ (U ∪ W)
    C.card = 4 ∧ ∀ x ∈ C,
      (∃! u, u ∈ U ∧ K.Adj x u) ∧ (∃! w, w ∈ W ∧ K.Adj x w) ∧
        ∃! y, y ∈ C ∧ K.Adj x y := by
  let C := (univ : Finset V) \ (U ∪ W)
  have hC : C.card = 4 := by
    change ((univ : Finset V) \ (U ∪ W)).card = 4
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hcard,
      card_union_of_disjoint hdis, hU, hW]
  have cover_pair (E : Finset V) (hE : E.card = 2) (hsub : E ⊆ U ∪ W)
      (hsep : ∀ u ∈ E, ∀ v ∈ E, u ≠ v → ∀ z, K.Adj u z → K.Adj v z → False)
      (x : V) (hx : x ∈ C) : ∃! a, a ∈ E ∧ K.Adj x a := by
    obtain ⟨a,b,hab,hEpair⟩ := card_eq_two.mp hE
    have ha : a ∈ E := by rw [hEpair]; simp
    have hb : b ∈ E := by rw [hEpair]; simp
    have inside (u : V) (hu : u ∈ E) : K.neighborFinset u ⊆ C := by
      intro v hv
      exact mem_sdiff.mpr ⟨mem_univ _, fun h => hind u (hsub hu) v h ((K.mem_neighborFinset _ _).mp hv)⟩
    have hDN : Disjoint (K.neighborFinset a) (K.neighborFinset b) := by
      apply Finset.disjoint_left.mpr
      intro v hva hvb
      exact hsep a ha b hb hab v ((K.mem_neighborFinset _ _).mp hva) ((K.mem_neighborFinset _ _).mp hvb)
    have hcover : K.neighborFinset a ∪ K.neighborFinset b = C := by
      apply eq_of_subset_of_card_le (union_subset (inside _ ha) (inside _ hb))
      rw [card_union_of_disjoint hDN, K.card_neighborFinset_eq_degree,
        K.card_neighborFinset_eq_degree, hdeg a, hdeg b, ite_eq_left (hsub ha),
        ite_eq_left (hsub hb), hC]
    have huniq (u v : V) (hu : u ∈ E ∧ K.Adj x u) (hv : v ∈ E ∧ K.Adj x v) : u = v := by
      by_contra h
      exact hsep u hu.1 v hv.1 h x hu.2.symm hv.2.symm
    have hx' : x ∈ K.neighborFinset a ∪ K.neighborFinset b := hcover.symm ▸ hx
    rcases mem_union.mp hx' with ha' | hb'
    · have he := And.intro ha ((K.mem_neighborFinset _ _).mp ha').symm
      exact ⟨a, he, fun _ h => huniq _ _ h he⟩
    · have he := And.intro hb ((K.mem_neighborFinset _ _).mp hb').symm
      exact ⟨b, he, fun _ h => huniq _ _ h he⟩
  refine ⟨hC, ?_⟩
  intro x hx
  have hu := cover_pair U hU (subset_union_left) hsepU x hx
  have hw := cover_pair W hW (subset_union_right) hsepW x hx
  refine ⟨hu, hw, ?_⟩
  have hu' : (U.filter (K.Adj x)).card = 1 := card_eq_one_iff_existsUnique.mpr (by
    simpa only [mem_filter] using hu)
  have hw' : (W.filter (K.Adj x)).card = 1 := card_eq_one_iff_existsUnique.mpr (by
    simpa only [mem_filter] using hw)
  have hUC : U ∪ W ∪ C = (univ : Finset V) := by
    change U ∪ W ∪ ((univ : Finset V) \ (U ∪ W)) = univ
    exact union_sdiff_of_subset (subset_univ _)
  have hD : Disjoint (U ∪ W) C := by
    apply Finset.disjoint_left.mpr
    exact fun _ h hx' => (mem_sdiff.mp hx').2 h
  have hd := K.card_neighborFinset_eq_degree x
  rw [K.neighborFinset_eq_filter, ← hUC, filter_union,
    card_union_of_disjoint (hD.mono (filter_subset _ _) (filter_subset _ _)), filter_union,
    card_union_of_disjoint (hdis.mono (filter_subset _ _) (filter_subset _ _)),
    hu', hw', hdeg x, ite_eq_right (mem_sdiff.mp hx).2] at hd
  apply (show (∃! a, a ∈ C.filter (K.Adj x)) → _ from
    fun h => by simpa only [mem_filter] using h)
  exact card_eq_one_iff_existsUnique.mp (Nat.add_left_cancel hd)

#print axioms separated_pairs_core

/-- Actual roots, ends and four core vertices for the two-high case. -/
private lemma two_high_core_shape
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {L R : Finset V}
    (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : Fintype.card (SideHigh G L) = 2) (hR : Fintype.card (SideHigh G R) = 8)
    (he : (compressed G L).edgeFinset.card = 1) :
    ∃ x y : SideHigh G L, (compressed G L).Adj x y ∧
      let A (r : SideHigh G L) := (univ : Finset (SideHigh G R)).filter
        (fun u => G.Adj r.val u.val)
      let U := A x
      let W := A y
      let C := univ \ (U ∪ W)
      let K := compressed G R
      U.card = 2 ∧ W.card = 2 ∧ Disjoint U W ∧ C.card = 4 ∧
      ∀ v ∈ C, (∃! u, u ∈ U ∧ K.Adj v u) ∧
        (∃! w, w ∈ W ∧ K.Adj v w) ∧ ∃! t, t ∈ C ∧ K.Adj v t := by
  obtain ⟨x, y, hxy, hU, hW, hdis, hind, hsep⟩ := two_high_end_sets hp hdeg hlow hg hL he
  let A (r : SideHigh G L) := (univ : Finset (SideHigh G R)).filter
    (fun u => G.Adj r.val u.val)
  let U := A x
  let W := A y
  let K := compressed G R
  have hRoots : ({x, y} : Finset (SideHigh G L)) = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_univ, hL]
    simp [hxy.ne]
  have adjX (v : SideHigh G R) : G.Adj v.val x.val ↔ v ∈ U := by
    simp [U, A, G.adj_comm]
  have adjY (v : SideHigh G R) : G.Adj v.val y.val ↔ v ∈ W := by
    simp [W, A, G.adj_comm]
  have degreeK (v : SideHigh G R) : K.degree v = if v ∈ U ∪ W then 2 else 3 := by
    have h := compressed_degree hp.symm hdeg hlow hg v
    rw [← side_high_neighbors_card hp.symm (mem_filter.mp v.property).1, ← hRoots] at h
    by_cases hu : v ∈ U
    · have hw : v ∉ W := Finset.disjoint_left.mp hdis hu
      have hx : G.Adj v.val x.val := (adjX v).mpr hu
      have hy : ¬ G.Adj v.val y.val := fun h => hw ((adjY v).mp h)
      have hd : K.degree v + 1 = 3 := by simpa [filter_insert, filter_singleton, hx, hy] using h
      rw [ite_eq_left (mem_union_left _ hu)]
      exact Nat.add_right_cancel (show K.degree v + 1 = 2 + 1 from hd)
    · have hx : ¬ G.Adj v.val x.val := fun h => hu ((adjX v).mp h)
      by_cases hw : v ∈ W
      · have hy : G.Adj v.val y.val := (adjY v).mpr hw
        have hd : K.degree v + 1 = 3 := by simpa [filter_insert, filter_singleton, hx, hy] using h
        rw [ite_eq_left (mem_union_right _ hw)]
        exact Nat.add_right_cancel (show K.degree v + 1 = 2 + 1 from hd)
      · have hy : ¬ G.Adj v.val y.val := fun h => hw ((adjY v).mp h)
        have hd : K.degree v = 3 := by simpa [filter_insert, filter_singleton, hx, hy] using h
        rw [ite_eq_right (fun hv => (mem_union.mp hv).elim hu hw)]
        exact hd
  obtain ⟨hC, core⟩ := separated_pairs_core K U W hR hU hW hdis hind
    (hsep x (by simp)) (hsep y (by simp)) degreeK
  exact ⟨x, y, hxy, hU, hW, hdis, hC, core⟩

#print axioms two_high_core_shape

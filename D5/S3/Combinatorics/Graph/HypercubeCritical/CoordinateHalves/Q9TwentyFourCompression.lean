import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta

/-! Degree and parity constraints for a twenty-four-point coordinate half. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open BalancedCubeLowerBound (coordinateSlice)
open GirthSliceCounting (degreeTwo degreeThree)
open private paritySide parity_bipartite parity_union parts_card sum_degrees_parts
  coordinate_slice_degree_cases coordinate_slice_low_independent low_slice_card_eq_q
  balanced_subset from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound

open private sum_high_neighbors sum_degree_parts neighbor_parts_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

attribute [local instance] Classical.propDecidable

/-- A twenty-four-point half has twelve independent degree-two vertices.
The two parts of its degree-three vertices have sizes two and ten, four and
eight, or six and six, up to swapping the two parts. -/
theorem half_degree_split {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 24) :
    let S := coordinateSlice C b
    let G := (hypercube 9).induce (S : Set (Q 9))
    let L := paritySide S false
    let R := paritySide S true
    (degreeTwo G univ).card = 12 ∧
    (∀ x y, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False) ∧
    (∑ v ∈ degreeThree G R, (degreeThree G (G.neighborFinset v)).card) = 6 ∧
    (degreeThree G L).card + (degreeThree G R).card = 12 ∧
    ((degreeThree G L).card = 2 ∨ (degreeThree G L).card = 4 ∨
      (degreeThree G L).card = 6 ∨ (degreeThree G L).card = 8 ∨
      (degreeThree G L).card = 10) := by
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S false
  let R := paritySide S true
  have hdeg (v : (S : Set (Q 9))) : G.degree v = 2 ∨ G.degree v = 3 :=
    coordinate_slice_degree_cases v.property hr
  have hind {x y : (S : Set (Q 9))} (hxy : G.Adj x y)
      (hx : G.degree x = 2) (hy : G.degree y = 2) : False :=
    coordinate_slice_low_independent hr hb hxy hx hy
  have hcut : 6 * directionEdges C 0 = C.card := by
    simpa using direction_edge_count (d := 3) C hr hb 0
  have hcount : (degreeTwo G univ).card = 12 := by
    rw [low_slice_card_eq_q hr]
    omega
  have hp : G.IsBipartiteWith (L : Set _) (R : Set _) := parity_bipartite S
  have hd : Disjoint L R := by simpa only [Finset.disjoint_coe] using hp.disjoint
  have hu : L ∪ R = univ := parity_union S
  have hab : L.card + R.card = 24 := by
    rw [← card_union_of_disjoint hd, hu, card_univ]
    simpa using hs
  have hd₂ : Disjoint (degreeTwo G L) (degreeTwo G R) :=
    hd.mono (filter_subset _ _) (filter_subset _ _)
  have hu₂ : degreeTwo G L ∪ degreeTwo G R = degreeTwo G univ := by
    simp only [degreeTwo, ← filter_union, hu]
  have hlows : (degreeTwo G L).card + (degreeTwo G R).card = 12 := by
    rw [← card_union_of_disjoint hd₂, hu₂, hcount]
  have hsum : 2 * (degreeTwo G L).card + 3 * (degreeThree G L).card =
      2 * (degreeTwo G R).card + 3 * (degreeThree G R).card :=
    (sum_degrees_parts G hdeg L).symm.trans
      ((SimpleGraph.isBipartiteWith_sum_degrees_eq hp).trans (sum_degrees_parts G hdeg R))
  have hL := parts_card G hdeg L
  have hR := parts_card G hdeg R
  have hhigh : (degreeThree G L).card + (degreeThree G R).card = 12 := by omega
  have hsplit : (degreeThree G L).card = 2 ∨ (degreeThree G L).card = 4 ∨
      (degreeThree G L).card = 6 ∨ (degreeThree G L).card = 8 ∨
      (degreeThree G L).card = 10 := by omega
  have hlowsRight :
      (∑ v ∈ degreeTwo G R, (degreeThree G (G.neighborFinset v)).card) =
        2 * (degreeTwo G R).card := by
    calc
      _ = ∑ _v ∈ degreeTwo G R, 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        have hv2 := (Finset.mem_filter.mp hv).2
        have hz : degreeTwo G (G.neighborFinset v) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro w hw
          obtain ⟨hwmem, hw2⟩ := Finset.mem_filter.mp hw
          exact hind ((G.mem_neighborFinset v w).mp hwmem) hv2 hw2
        have hn : (degreeTwo G (G.neighborFinset v)).card +
            (degreeThree G (G.neighborFinset v)).card = G.degree v :=
          neighbor_parts_card hdeg v
        rw [hz, Finset.card_empty, zero_add] at hn
        exact hn.trans hv2
      _ = _ := by simp [Nat.mul_comm]
  have hinc :=
    (sum_degree_parts hdeg R (fun v => (degreeThree G (G.neighborFinset v)).card)).symm.trans
      (sum_high_neighbors hp)
  rw [hlowsRight] at hinc
  have hdirect : (∑ v ∈ degreeThree G R, (degreeThree G (G.neighborFinset v)).card) = 6 := by
    omega
  exact ⟨hcount, fun _ _ hxy hx hy => hind hxy hx hy, hdirect, hhigh, hsplit⟩

#print axioms half_degree_split

open private SideHigh compressed compressed_degree compressed_triangle_free from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private side_high_neighbors_card high_neighbors_compressed_separated from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta

section SuppressVertices

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {L R : Finset V}

/-- Keep original edges between high vertices, and replace each two-edge path
through a low vertex by an edge in its high endpoints' parity class. -/
private def suppress (G : SimpleGraph V) (L R : Finset V) :
    SimpleGraph (SideHigh G L ⊕ SideHigh G R) where
  Adj
    | .inl x, .inl y => (compressed G L).Adj x y
    | .inr x, .inr y => (compressed G R).Adj x y
    | .inl x, .inr y => G.Adj x.val y.val
    | .inr x, .inl y => G.Adj x.val y.val
  symm := by
    constructor
    intro x y h
    cases x <;> cases y
    · exact (compressed G L).adj_symm h
    · exact G.adj_symm h
    · exact G.adj_symm h
    · exact (compressed G R).adj_symm h
  loopless := by
    constructor
    intro x h
    cases x
    · exact (compressed G L).loopless.irrefl _ h
    · exact (compressed G R).loopless.irrefl _ h

private theorem suppress_regular (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) : (suppress G L R).IsRegularOfDegree 3 := by
  classical
  let J := suppress G L R
  let l : SideHigh G L ↪ SideHigh G L ⊕ SideHigh G R := ⟨Sum.inl, Sum.inl_injective⟩
  let r : SideHigh G R ↪ SideHigh G L ⊕ SideHigh G R := ⟨Sum.inr, Sum.inr_injective⟩
  intro u
  cases u with
  | inl x =>
    let A := ((compressed G L).neighborFinset x).map l
    let B := ((univ : Finset (SideHigh G R)).filter (fun y => G.Adj x.val y.val)).map r
    have hN : J.neighborFinset (.inl x) = A ∪ B := by
      ext y
      rw [SimpleGraph.mem_neighborFinset]
      cases y <;> simp [J, suppress, A, B, l, r, SimpleGraph.mem_neighborFinset]
    have hd : Disjoint A B := by simp [A, B, l, r, Finset.disjoint_left]
    have h := compressed_degree hp hdeg (fun hxy hx hy => hlow hxy hx hy) hg x
    have hs := side_high_neighbors_card hp (mem_filter.mp x.property).1
    change J.degree (.inl x) = 3
    rw [← J.card_neighborFinset_eq_degree, hN, card_union_of_disjoint hd]
    rw [show A.card = (compressed G L).degree x by simp [A], show B.card = _ by
      rw [show B = _ by rfl, card_map, hs]]
    exact h
  | inr y =>
    let A := ((univ : Finset (SideHigh G L)).filter (fun x => G.Adj y.val x.val)).map l
    let B := ((compressed G R).neighborFinset y).map r
    have hN : J.neighborFinset (.inr y) = A ∪ B := by
      ext x
      rw [SimpleGraph.mem_neighborFinset]
      cases x <;> simp [J, suppress, A, B, l, r, SimpleGraph.mem_neighborFinset]
    have hd : Disjoint A B := by simp [A, B, l, r, Finset.disjoint_left]
    have h := compressed_degree hp.symm hdeg (fun hxy hx hy => hlow hxy hx hy) hg y
    have hs := side_high_neighbors_card hp.symm (mem_filter.mp y.property).1
    change J.degree (.inr y) = 3
    rw [← J.card_neighborFinset_eq_degree, hN, card_union_of_disjoint hd]
    rw [show B.card = (compressed G R).degree y by simp [B], show A.card = _ by
      rw [show A = _ by rfl, card_map, hs], Nat.add_comm]
    exact h

private theorem suppress_triangle_free (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) :
    ∀ x y z, (suppress G L R).Adj x y → (suppress G L R).Adj y z →
      (suppress G L R).Adj z x → False := by
  have mainLeft {x y : SideHigh G L} {z : SideHigh G R}
      (hxy : (compressed G L).Adj x y) (hyz : G.Adj y.val z.val)
      (hzx : G.Adj z.val x.val) : False :=
    (high_neighbors_compressed_separated hp.symm hg (mem_filter.mp z.property).1
      (mem_filter.mp z.property).2 hzx (G.adj_symm hyz) (hxy.ne)).1 hxy
  have mainRight {x y : SideHigh G R} {z : SideHigh G L}
      (hxy : (compressed G R).Adj x y) (hyz : G.Adj y.val z.val)
      (hzx : G.Adj z.val x.val) : False :=
    (high_neighbors_compressed_separated hp hg (mem_filter.mp z.property).1
      (mem_filter.mp z.property).2 hzx (G.adj_symm hyz) (hxy.ne)).1 hxy
  intro x y z a b c
  cases x <;> cases y <;> cases z
  · exact compressed_triangle_free hp hg _ _ _ a b c
  · exact mainLeft a b c
  · exact mainLeft c a b
  · exact mainRight b c a
  · exact mainLeft b c a
  · exact mainRight c a b
  · exact mainRight a b c
  · exact compressed_triangle_free hp.symm hg _ _ _ a b c

open private one_three_cross_impossible three_walk_endpoint_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

private theorem no_square_through_direct_edge
    (hp : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (x : SideHigh G L) (y : SideHigh G R)
    (z t : SideHigh G L ⊕ SideHigh G R) (hxy : G.Adj x.val y.val)
    (hyz : (suppress G L R).Adj (.inr y) z) (hzt : (suppress G L R).Adj z t)
    (htx : (suppress G L R).Adj t (.inl x))
    (hxz : Sum.inl x ≠ z) (hyt : Sum.inr y ≠ t) : False := by
  obtain ⟨hxL, hx3⟩ := mem_filter.mp x.property
  obtain ⟨hyR, hy3⟩ := mem_filter.mp y.property
  cases z with
  | inl z =>
    have hxz' : x ≠ z := fun h => hxz (congrArg Sum.inl h)
    cases t with
    | inl t =>
      exact (high_neighbors_compressed_separated hp.symm hg hyR hy3 hxy.symm hyz hxz').2
        t (show (compressed G L).Adj t x from htx).symm hzt
    | inr t =>
      exact one_three_cross_impossible hp hg hxL hxL hxy
        (show G.Adj t.val x.val from htx).symm
        (show G.Adj z.val t.val from hzt).symm (show G.Adj y.val z.val from hyz).symm
        (fun h => hxz' (Subtype.ext h))
        (fun h => hyt (congrArg Sum.inr (Subtype.ext h.symm))) ⟨rfl, rfl⟩
  | inr z =>
    cases t with
    | inr t =>
      exact (high_neighbors_compressed_separated hp hg hxL hx3 hxy
        (show G.Adj t.val x.val from htx).symm (fun h => hyt (congrArg Sum.inr h))).2
        z hyz (show (compressed G R).Adj z t from hzt).symm
    | inl t =>
      obtain ⟨hyz', m, hm2, hym, hzm⟩ := show (compressed G R).Adj y z from hyz
      obtain ⟨htx', n, hn2, htn, hxn⟩ := show (compressed G L).Adj t x from htx
      have he := three_walk_endpoint_injective hp hg hxL hxL
        hxy hym hzm.symm hxn htn.symm
        (show G.Adj z.val t.val from hzt).symm
        (by intro h; have := h ▸ hx3; omega)
        (fun h => hyz' (Subtype.ext h))
        (fun h => htx' (Subtype.ext h.symm))
        (by intro h; have hz3 := (mem_filter.mp z.property).2; rw [← h] at hz3; omega)
        ⟨rfl, rfl⟩
      have := he.2.1 ▸ hy3
      omega

end SuppressVertices

/-- In a triangle-free cubic graph on twelve vertices, disconnection forces
every edge to lie on a four-cycle. -/
private theorem connected_of_edge_without_square {W : Type*} [Fintype W] [DecidableEq W]
    {J : SimpleGraph W} [DecidableRel J.Adj] (hcard : Fintype.card W = 12)
    (hr : J.IsRegularOfDegree 3)
    (htri : ∀ u v w, J.Adj u v → J.Adj v w → J.Adj w u → False)
    {a b : W} (hab : J.Adj a b)
    (hno : ∀ c d, J.Adj b c → J.Adj c d → J.Adj d a → a ≠ c → b ≠ d → False) :
    J.Connected := by
  classical
  have hdegree (x : W) : (J.neighborFinset x).card = 3 :=
    (J.card_neighborFinset_eq_degree x).trans (hr x)
  have hdisjoint {x y : W} (hxy : J.Adj x y) :
      Disjoint (J.neighborFinset x) (J.neighborFinset y) := by
    apply Finset.disjoint_left.mpr
    intro z hx hy
    exact htri _ _ _ hxy ((J.mem_neighborFinset _ _).mp hy)
      ((J.mem_neighborFinset _ _).mp hx).symm
  refine J.connected_iff_exists_forall_reachable.mpr ⟨a, ?_⟩
  intro w
  by_contra hnot
  let D := (univ : Finset W).filter (J.Reachable a)
  let A := J.neighborFinset a ∪ J.neighborFinset b
  have hA : A ⊆ D := by
    intro z hz
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rcases mem_union.mp hz with hz | hz
    · exact ((J.mem_neighborFinset _ _).mp hz).reachable
    · exact hab.reachable.trans ((J.mem_neighborFinset _ _).mp hz).reachable
  have hAc : A.card = 6 := by
    rw [show A = _ by rfl, card_union_of_disjoint (hdisjoint hab), hdegree, hdegree]
  obtain ⟨w', hw'⟩ : (J.neighborFinset w).Nonempty := by
    apply Finset.card_pos.mp
    rw [hdegree]
    decide
  have hww' := (J.mem_neighborFinset _ _).mp hw'
  let B := J.neighborFinset w ∪ J.neighborFinset w'
  have hB : B ⊆ (univ : Finset W) \ D := by
    intro z hz
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro h
    have haz := (mem_filter.mp h).2
    apply hnot
    rcases mem_union.mp hz with hz | hz
    · exact haz.trans ((J.mem_neighborFinset _ _).mp hz).reachable.symm
    · exact haz.trans (((J.mem_neighborFinset _ _).mp hz).reachable.symm.trans hww'.reachable.symm)
  have hBc : B.card = 6 := by
    rw [show B = _ by rfl, card_union_of_disjoint (hdisjoint hww'), hdegree, hdegree]
  have hd := card_le_card hB
  rw [hBc] at hd
  have hDA : A = D := by
    apply eq_of_subset_of_card_le hA
    have hcount := card_sdiff_add_card_eq_card (subset_univ D)
    rw [card_univ, hcard] at hcount
    omega
  have hother (x y : W) : ∃ z ∈ J.neighborFinset x, z ≠ y := by
    by_contra! h
    have hs : J.neighborFinset x ⊆ {y} := fun z hz => mem_singleton.mpr (h z hz)
    have hc := card_le_card hs
    rw [hdegree, card_singleton] at hc
    omega
  obtain ⟨c, hcb, hca⟩ := hother b a
  obtain ⟨d, hda, hdb⟩ := hother a b
  have hbc := (J.mem_neighborFinset _ _).mp hcb
  have hcd : J.Adj c d := by
    have hs : J.neighborFinset c ⊆ J.neighborFinset a := by
      intro z hz
      have hcz := (J.mem_neighborFinset _ _).mp hz
      have hdz : z ∈ D := mem_filter.mpr ⟨mem_univ _,
        hab.reachable.trans (hbc.reachable.trans hcz.reachable)⟩
      rw [← hDA] at hdz
      rcases mem_union.mp hdz with hz | hz
      · exact hz
      · exact (Finset.disjoint_left.mp (hdisjoint hbc) hz
          (show z ∈ J.neighborFinset c from (J.mem_neighborFinset _ _).mpr hcz)).elim
    have he : J.neighborFinset c = J.neighborFinset a :=
      eq_of_subset_of_card_le hs (by rw [hdegree, hdegree])
    exact (J.mem_neighborFinset _ _).mp (he.symm ▸ hda)
  exact hno c d hbc hcd ((J.mem_neighborFinset _ _).mp hda).symm hca.symm hdb.symm

/-- Suppressing all twelve degree-two vertices in a twenty-four-point half
gives a connected triangle-free cubic graph on twelve vertices. -/
theorem half_suppression {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 24) :
    let S := coordinateSlice C b
    let G := (hypercube 9).induce (S : Set (Q 9))
    let L := paritySide S false
    let R := paritySide S true
    let J := suppress G L R
    Fintype.card (SideHigh G L ⊕ SideHigh G R) = 12 ∧
      J.IsRegularOfDegree 3 ∧
      (∀ x y z, J.Adj x y → J.Adj y z → J.Adj z x → False) ∧ J.Connected := by
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S false
  let R := paritySide S true
  have hp : G.IsBipartiteWith (L : Set _) (R : Set _) := parity_bipartite S
  have hg : (8 : ℕ∞) ≤ G.egirth :=
    BalancedCubeGirth.eight_le_egirth S (balanced_subset hb (filter_subset _ _))
  obtain ⟨_, hlow, hdirect, hhigh, _⟩ := half_degree_split hC hr hb b hs
  have hdeg (v : (S : Set (Q 9))) : G.degree v = 2 ∨ G.degree v = 3 :=
    coordinate_slice_degree_cases v.property hr
  have hc : Fintype.card (SideHigh G L ⊕ SideHigh G R) = 12 := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
    exact hhigh
  have hj := suppress_regular hp hdeg (hlow _ _) hg
  have ht := suppress_triangle_free hp hg
  have he : ∃ y ∈ degreeThree G R, 0 < (degreeThree G (G.neighborFinset y)).card := by
    by_contra! h
    have hz : (∑ y ∈ degreeThree G R, (degreeThree G (G.neighborFinset y)).card) = 0 := by
      exact Finset.sum_eq_zero (fun y hy => Nat.eq_zero_of_le_zero (h y hy))
    have hh : (0 : Nat) = 6 := hz.symm.trans hdirect
    omega
  obtain ⟨y, hy, hpY⟩ := he
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpY
  obtain ⟨hxN, hx3⟩ := Finset.mem_filter.mp hx
  have hxy := (G.mem_neighborFinset _ _).mp hxN
  have hxL : x ∈ L := hp.mem_of_mem_adj' (mem_filter.mp hy).1 hxy.symm
  let a : SideHigh G L := ⟨x, mem_filter.mpr ⟨hxL, hx3⟩⟩
  let b' : SideHigh G R := ⟨y, hy⟩
  have hab : (suppress G L R).Adj (.inl a) (.inr b') := hxy.symm
  exact ⟨hc, hj, ht, connected_of_edge_without_square hc hj ht hab
    (fun c d => no_square_through_direct_edge hp hg a b' c d hxy.symm)⟩

#print axioms half_suppression

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression

/-! A cubic graph with at most fourteen vertices is connected if it has
no triangles and some edge belongs to no four-cycle. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixCompression

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
open private SideHigh from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private suppress suppress_regular suppress_triangle_free no_square_through_direct_edge from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression

attribute [local instance] Classical.propDecidable

private theorem connected_of_edge_without_square {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hcard : Fintype.card V ≤ 14)
    (hreg : G.IsRegularOfDegree 3)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False)
    {a b : V} (hab : G.Adj a b)
    (hno : ∀ c d, G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d → False) :
    G.Connected := by
  classical
  let N := G.neighborFinset
  have hN (x : V) : (N x).card = 3 := (G.card_neighborFinset_eq_degree x).trans (hreg x)
  have nd {x y : V} (hxy : G.Adj x y) : Disjoint (N x) (N y) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact htri x y z hxy ((G.mem_neighborFinset _ _).mp hz')
      ((G.mem_neighborFinset _ _).mp hz).symm
  refine G.connected_iff_exists_forall_reachable.mpr ⟨a, fun w => ?_⟩
  by_contra hn
  let D := univ.filter (G.Reachable a)
  let A := N a ∪ N b
  have ha : A ⊆ D := by
    intro x hx
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rcases mem_union.mp hx with hx | hx
    · exact ((G.mem_neighborFinset _ _).mp hx).reachable
    · exact hab.reachable.trans ((G.mem_neighborFinset _ _).mp hx).reachable
  have hAc : A.card = 6 := by rw [show A = _ from rfl, card_union_of_disjoint (nd hab), hN, hN]
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < (N w).card by rw [hN]; decide)
  have hwv := (G.mem_neighborFinset _ _).mp hv
  have hB : N w ∪ N v ⊆ univ \ D := by
    intro x hx
    refine mem_sdiff.mpr ⟨mem_univ _, fun hx' => hn ?_⟩
    have hr := (mem_filter.mp hx').2
    rcases mem_union.mp hx with hx | hx
    · exact hr.trans ((G.mem_neighborFinset _ _).mp hx).reachable.symm
    · exact (hr.trans ((G.mem_neighborFinset _ _).mp hx).reachable.symm).trans hwv.reachable.symm
  have hc := card_le_card hB
  rw [card_union_of_disjoint (nd hwv), hN, hN] at hc
  let T := D \ A
  have ht : T.card ≤ 2 := by
    have h₁ := card_sdiff_add_card_eq_card ha
    have h₂ := card_sdiff_add_card_eq_card (subset_univ D)
    rw [card_univ] at h₂
    change T.card + A.card = D.card at h₁
    omega
  let L := (N a).erase b
  let R := (N b).erase a
  have hLc : L.card = 2 := by
    have h := card_erase_add_one ((G.mem_neighborFinset a b).mpr hab)
    change L.card + 1 = (N a).card at h
    rw [hN] at h
    omega
  have hRc : R.card = 2 := by
    have h := card_erase_add_one ((G.mem_neighborFinset b a).mpr hab.symm)
    change R.card + 1 = (N b).card at h
    rw [hN] at h
    omega
  have outside (x parent : V) (hxp : G.Adj x parent)
      (hreach : G.Reachable a x) (hinside : ∀ z ∈ N x, z ∈ A → z = parent) :
      (N x).erase parent ⊆ T := by
    intro z hz
    obtain ⟨hne, hz⟩ := mem_erase.mp hz
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,
      hreach.trans ((G.mem_neighborFinset _ _).mp hz).reachable⟩,
      fun hm => hne (hinside z hz hm)⟩
  have outside_two (x parent : V) (hxp : G.Adj x parent)
      (hsub : (N x).erase parent ⊆ T) : (N x).erase parent = T := by
    have h := card_erase_add_one ((G.mem_neighborFinset _ _).mpr hxp)
    change ((N x).erase parent).card + 1 = (N x).card at h
    rw [hN] at h
    exact eq_of_subset_of_card_le hsub (by omega)
  have left_all (x : V) (hx : x ∈ L) : (N x).erase a = T := by
    obtain ⟨hne, hx'⟩ := mem_erase.mp hx
    have hax := (G.mem_neighborFinset _ _).mp hx'
    apply outside_two x a hax.symm
    apply outside x a hax.symm hax.reachable
    intro z hz hzA
    rcases mem_union.mp hzA with hzA | hzA
    · exact (Finset.disjoint_left.mp (nd hax) hzA hz).elim
    · by_contra hza
      exact hno z x ((G.mem_neighborFinset _ _).mp hzA)
        ((G.mem_neighborFinset _ _).mp hz).symm hax.symm (Ne.symm hza) (Ne.symm hne)
  have right_all (x : V) (hx : x ∈ R) : (N x).erase b = T := by
    obtain ⟨hne, hx'⟩ := mem_erase.mp hx
    have hbx := (G.mem_neighborFinset _ _).mp hx'
    apply outside_two x b hbx.symm
    apply outside x b hbx.symm (hab.reachable.trans hbx.reachable)
    intro z hz hzA
    rcases mem_union.mp hzA with hzA | hzA
    · by_contra hzb
      exact hno x z hbx ((G.mem_neighborFinset _ _).mp hz)
        ((G.mem_neighborFinset _ _).mp hzA).symm hne.symm (Ne.symm hzb)
    · exact (Finset.disjoint_left.mp (nd hbx) hzA hz).elim
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < L.card by rw [hLc]; decide)
  have hxp := ((G.mem_neighborFinset _ _).mp (mem_erase.mp hx).2).symm
  have he := card_erase_add_one ((G.mem_neighborFinset _ _).mpr hxp)
  rw [left_all x hx, hN] at he
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  have hsub : L ∪ R ⊆ N z := by
    intro y hy
    rcases mem_union.mp hy with hy | hy
    · have hd := (mem_erase.mp ((left_all y hy).symm ▸ hz)).2
      exact (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hd).symm
    · have hd := (mem_erase.mp ((right_all y hy).symm ▸ hz)).2
      exact (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hd).symm
  have hd := card_le_card hsub
  have hlr : Disjoint L R := (nd hab).mono (erase_subset _ _) (erase_subset _ _)
  rw [card_union_of_disjoint hlr, hLc, hRc, hN] at hd
  omega

/-- A twenty-six-point coordinate half compresses to a connected triangle-free
cubic graph on fourteen vertices with nine edges between its parity classes.
The smaller parity class has size three, five, or seven. -/
theorem half_suppression {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 26) :
    let S := coordinateSlice C b
    let G := (hypercube 9).induce (S : Set (Q 9))
    let L := paritySide S false
    let R := paritySide S true
    let J := suppress G L R
    Fintype.card (SideHigh G L ⊕ SideHigh G R) = 14 ∧
      J.IsRegularOfDegree 3 ∧ (∀ x y z, J.Adj x y → J.Adj y z → J.Adj z x → False) ∧
      J.Connected ∧
      (∑ v ∈ degreeThree G R, (degreeThree G (G.neighborFinset v)).card) = 9 ∧
      let n := min (degreeThree G L).card (degreeThree G R).card
      n = 3 ∨ n = 5 ∨ n = 7 := by
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S false
  let R := paritySide S true
  have hp : G.IsBipartiteWith (L : Set _) (R : Set _) := parity_bipartite S
  have hg : (8 : ℕ∞) ≤ G.egirth :=
    BalancedCubeGirth.eight_le_egirth S (balanced_subset hb (filter_subset _ _))
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
  have hd : Disjoint L R := Finset.disjoint_coe.mp hp.disjoint
  have hu : L ∪ R = univ := parity_union S
  have hab : L.card + R.card = 26 := by
    rw [← card_union_of_disjoint hd, hu, card_univ]
    exact (Fintype.card_coe S).trans hs
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
  have hc : Fintype.card (SideHigh G L ⊕ SideHigh G R) = 14 := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
    omega
  have hsize : let n := min (degreeThree G L).card (degreeThree G R).card
      n = 3 ∨ n = 5 ∨ n = 7 := by
    dsimp only
    omega
  have hlowsRight :
      (∑ v ∈ degreeTwo G R, (degreeThree G (G.neighborFinset v)).card) =
        2 * (degreeTwo G R).card := by
    calc
      _ = ∑ _v ∈ degreeTwo G R, 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        have hv2 := (mem_filter.mp hv).2
        have he : degreeTwo G (G.neighborFinset v) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro w hw
          obtain ⟨hN, hw2⟩ := mem_filter.mp hw
          exact hind ((G.mem_neighborFinset v w).mp hN) hv2 hw2
        have h : (degreeTwo G (G.neighborFinset v)).card +
            (degreeThree G (G.neighborFinset v)).card = G.degree v :=
          neighbor_parts_card hdeg v
        rw [he, card_empty, zero_add] at h
        exact h.trans hv2
      _ = _ := by simp [Nat.mul_comm]
  have hinc :=
    (sum_degree_parts hdeg R (fun v => (degreeThree G (G.neighborFinset v)).card)).symm.trans
      (sum_high_neighbors hp)
  rw [hlowsRight] at hinc
  have hdirect : (∑ v ∈ degreeThree G R, (degreeThree G (G.neighborFinset v)).card) = 9 := by
    omega
  have he : ∃ y ∈ degreeThree G R, 0 < (degreeThree G (G.neighborFinset y)).card := by
    by_contra! h
    have hz : (∑ y ∈ degreeThree G R, (degreeThree G (G.neighborFinset y)).card) = 0 :=
      Finset.sum_eq_zero (fun y hy => Nat.eq_zero_of_le_zero (h y hy))
    omega
  obtain ⟨y, hy, hY⟩ := he
  obtain ⟨x, hx⟩ := card_pos.mp hY
  obtain ⟨hxN, hx3⟩ := mem_filter.mp hx
  have hxy := (G.mem_neighborFinset _ _).mp hxN
  have hxL : x ∈ L := hp.mem_of_mem_adj' (mem_filter.mp hy).1 hxy.symm
  let a : SideHigh G L := ⟨x, mem_filter.mpr ⟨hxL, hx3⟩⟩
  let z : SideHigh G R := ⟨y, hy⟩
  have haz : (suppress G L R).Adj (.inl a) (.inr z) := hxy.symm
  have hj := suppress_regular hp hdeg (fun hxy hx hy => hind hxy hx hy) hg
  have ht := suppress_triangle_free hp hg
  have hconn := connected_of_edge_without_square hc.le hj ht haz
    (fun c d => no_square_through_direct_edge hp hg a z c d hxy.symm)
  exact ⟨hc, hj, ht, hconn, hdirect, hsize⟩

#print axioms connected_of_edge_without_square
#print axioms half_suppression

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentySixCompression

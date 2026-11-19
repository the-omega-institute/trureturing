import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric

/-! Actual low-path compression of a balanced twenty-one-vertex cube slice. -/

set_option autoImplicit false
noncomputable section

open Finset SimpleGraph
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
open GirthSliceCounting (degreeTwo degreeThree)
attribute [local instance] Classical.propDecidable

open private SideHigh compressed compressed_degree compressed_triangle_free from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private three_walk_endpoint_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private side_high_neighbors_card high_neighbors_compressed_separated from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta
open private compressed_edge_count from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric
open private paritySide parity_bipartite parity_union parts_card sum_degrees_parts from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound

/-- The high vertices of a twenty-one-point slice split as two and eight or four and six. -/
private lemma twenty_one_high_parity_split (S : Finset (Q 9)) (hS : S.card = 21)
    (hdeg : ∀ v, ((hypercube 9).induce (S : Set (Q 9))).degree v = 2 ∨
      ((hypercube 9).induce (S : Set (Q 9))).degree v = 3)
    (hcount : (degreeTwo ((hypercube 9).induce (S : Set (Q 9))) univ).card = 11) :
    ∃ b : Bool,
      let G := (hypercube 9).induce (S : Set (Q 9))
      let L := paritySide S b
      let R := paritySide S (!b)
      ((degreeThree G L).card = 2 ∧ (degreeThree G R).card = 8 ∧
        (degreeTwo G L).card = 10 ∧ (degreeTwo G R).card = 1) ∨
      ((degreeThree G L).card = 4 ∧ (degreeThree G R).card = 6 ∧
        (degreeTwo G L).card = 7 ∧ (degreeTwo G R).card = 4) := by
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S false
  let R := paritySide S true
  have hp : G.IsBipartiteWith (L : Set (S : Set (Q 9))) (R : Set (S : Set (Q 9))) :=
    parity_bipartite S
  have hd : Disjoint L R := by simpa only [Finset.disjoint_coe] using hp.disjoint
  have hu : L ∪ R = univ := parity_union S
  have hab : L.card + R.card = 21 := by
    rw [← card_union_of_disjoint hd, hu, card_univ]
    simpa using hS
  have hd₂ : Disjoint (degreeTwo G L) (degreeTwo G R) :=
    hd.mono (filter_subset _ _) (filter_subset _ _)
  have hu₂ : degreeTwo G L ∪ degreeTwo G R = degreeTwo G univ := by
    simp only [degreeTwo, ← filter_union, hu]
  have hlows : (degreeTwo G L).card + (degreeTwo G R).card = 11 := by
    rw [← card_union_of_disjoint hd₂, hu₂, hcount]
  have hsum : 2 * (degreeTwo G L).card + 3 * (degreeThree G L).card =
      2 * (degreeTwo G R).card + 3 * (degreeThree G R).card := by
    calc
      _ = ∑ v ∈ L, G.degree v := (sum_degrees_parts G hdeg L).symm
      _ = ∑ v ∈ R, G.degree v := SimpleGraph.isBipartiteWith_sum_degrees_eq hp
      _ = _ := sum_degrees_parts G hdeg R
  have hL := parts_card G hdeg L
  have hR := parts_card G hdeg R
  have htotal : (degreeThree G L).card + (degreeThree G R).card = 10 := by omega
  have hsplit : (degreeThree G L).card = 2 ∨ (degreeThree G L).card = 4 ∨
      (degreeThree G L).card = 6 ∨ (degreeThree G L).card = 8 := by omega
  have hcases (i : ℕ) (hi : (degreeThree G L).card = i) :
      (degreeThree G R).card = 10 - i ∧
        2 * (degreeTwo G L).card + 3 * i =
          2 * (degreeTwo G R).card + 3 * (10 - i) := by omega
  rcases hsplit with h | h | h | h
  · have ⟨hR8, e⟩ := hcases 2 h
    have hl : (degreeTwo G L).card = 10 := by omega
    have hr : (degreeTwo G R).card = 1 := by omega
    exact ⟨false, Or.inl ⟨h, hR8, hl, hr⟩⟩
  · have ⟨hR6, e⟩ := hcases 4 h
    have hl : (degreeTwo G L).card = 7 := by omega
    have hr : (degreeTwo G R).card = 4 := by omega
    exact ⟨false, Or.inr ⟨h, hR6, hl, hr⟩⟩
  · have ⟨hR4, e⟩ := hcases 6 h
    have hl : (degreeTwo G R).card = 7 := by omega
    have hr : (degreeTwo G L).card = 4 := by omega
    exact ⟨true, Or.inr ⟨hR4, h, hl, hr⟩⟩
  · have ⟨hR2, e⟩ := hcases 8 h
    have hl : (degreeTwo G R).card = 10 := by omega
    have hr : (degreeTwo G L).card = 1 := by omega
    exact ⟨true, Or.inl ⟨hR2, h, hl, hr⟩⟩

#print axioms twenty_one_high_parity_split

private lemma four_edges_on_four_vertices
    {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hV : Fintype.card V = 4) (hE : H.edgeFinset.card = 4)
    (htri : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False) :
    ∀ x, H.degree x = 2 := by
  classical
  have hsum := H.sum_degrees_eq_twice_card_edges
  rw [hE] at hsum
  have hbound (x : V) : H.degree x ≤ 2 := by
    by_contra! hgt
    have hxlt := H.degree_lt_card_verts x
    have hx3 : H.degree x = Fintype.card V - 1 := by omega
    have hxu := (H.degree_eq_card_sub_one x).mp hx3
    have hd (y : V) : H.degree y ≤ if y = x then 3 else 1 := by
      by_cases hy : y = x
      · subst y
        simpa [hV] using hx3.le
      simp only [ite_eq_right hy]
      rw [← H.card_neighborFinset_eq_degree y, ← Finset.card_singleton x]
      apply card_le_card
      intro z hz
      have hyz := (H.mem_neighborFinset y z).mp hz
      by_contra hz'
      have hzx : z ≠ x := by simpa using hz'
      exact htri x y z (hxu (Ne.symm hy)) hyz (hxu (Ne.symm hzx)).symm
    have hu := sum_le_sum (s := (univ : Finset V)) (fun y _ => hd y)
    have hweights : (∑ y : V, if y = x then 3 else 1) = 6 := by
      rw [← sum_erase_add _ _ (mem_univ x), ite_eq_left rfl]
      have he : (∑ y ∈ (univ : Finset V).erase x, if y = x then 3 else 1) =
          ∑ _y ∈ (univ : Finset V).erase x, 1 := by
        apply sum_congr rfl
        intro y hy
        rw [ite_eq_right (mem_erase.mp hy).1]
      rw [he, sum_const, card_erase_of_mem (mem_univ x), card_univ, hV]
      decide
    rw [hweights] at hu
    omega
  intro x
  by_contra hx
  have hlt : H.degree x < 2 := by have hb := hbound x; omega
  have hs := sum_lt_sum (s := (univ : Finset V))
    (fun y _ => hbound y) ⟨x, mem_univ _, hlt⟩
  simp only [sum_const, card_univ, hV, smul_eq_mul] at hs
  omega

private lemma two_regular_cycle_of_small_card
    {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hV : Fintype.card V = 4) (hdegree : ∀ x, H.degree x = 2) :
    Nonempty (cycleGraph 4 ≃g H) := by
  classical
  have hn : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let a : V := Classical.choice hn
  have hcycles : H.IsCycles := by
    intro v _
    rw [H.ncard_neighborSet, hdegree]
  have hneighbor (v : V) : (H.neighborSet v).Nonempty := by
    apply (H.degree_pos_iff_nonempty).mp
    rw [hdegree]
    decide
  obtain ⟨p, hp, hpc⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := H.connectedComponentMk a) (v := a) rfl (hneighbor a)
  have hcomponent (v : V) : H.Reachable a v ↔ v ∈ p.support := by
    rw [← p.mem_verts_toSubgraph, hpc, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq]
    exact reachable_comm
  have hcover (v : V) : v ∈ p.support := by
    by_contra hv
    obtain ⟨q, hq, _⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := H.connectedComponentMk v) (v := v) rfl (hneighbor v)
    have hdis : Disjoint p.support.toFinset q.support.toFinset := by
      apply Finset.disjoint_left.mpr
      intro z hzp hzq
      obtain ⟨r, _, _⟩ := q.mem_support_iff_exists_append.mp (List.mem_toFinset.mp hzq)
      exact hv ((hcomponent v).mp
        (((hcomponent z).mpr (List.mem_toFinset.mp hzp)).trans r.reachable.symm))
    have hc := card_le_card (subset_univ (p.support.toFinset ∪ q.support.toFinset))
    rw [card_union_of_disjoint hdis, hp.support_toFinset_card, hq.support_toFinset_card,
      card_univ, hV] at hc
    have hp3 := hp.isCircuit.three_le_length
    have hq3 := hq.isCircuit.three_le_length
    omega
  have hc : H.Connected := ⟨fun u v =>
    ((hcomponent u).mpr (hcover u)).symm.trans ((hcomponent v).mpr (hcover v))⟩
  have hiso := SimpleGraph.cycle_iso_of_connected_degree_le_two H hc
    (H.maxDegree_le_of_forall_degree_le 2 (fun v => (hdegree v).le)) p hp
  have hu : p.support.toFinset = (univ : Finset V) := by ext v; simp [hcover v]
  have hlen : p.length = 4 := by rw [← hp.support_toFinset_card, hu, card_univ, hV]
  change Nonempty (cycleGraph p.length ≃g H) at hiso
  rwa [hlen] at hiso

/-- A hypothetical 21-point half has either one compressed edge on the smaller side
or a compressed square whose four high vertices each have one actual high neighbor. -/
private lemma twenty_one_slice_compression
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
      (Fintype.card (SideHigh G L) = 2 ∧ Fintype.card (SideHigh G R) = 8 ∧
        (compressed G L).edgeFinset.card = 1 ∧ (compressed G R).edgeFinset.card = 10) ∨
      (Nonempty (cycleGraph 4 ≃g compressed G L) ∧
        Fintype.card (SideHigh G R) = 6 ∧ (compressed G R).edgeFinset.card = 7 ∧
        ∀ x : SideHigh G L, (degreeThree G (G.neighborFinset x.val)).card = 1) := by
  obtain ⟨b, hcases⟩ := twenty_one_high_parity_split S hS hdeg hcount
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S b
  let R := paritySide S (!b)
  have hpart : G.IsBipartiteWith (L : Set (S : Set (Q 9))) (R : Set (S : Set (Q 9))) := by
    cases b
    · exact parity_bipartite S
    · exact (parity_bipartite S).symm
  have hg := BalancedCubeGirth.eight_le_egirth S hb
  have heL := compressed_edge_count hpart hdeg (fun hxy hx hy => hlow hxy hx hy) hg
  have heR := compressed_edge_count hpart.symm hdeg (fun hxy hx hy => hlow hxy hx hy) hg
  have hcard (T : Finset (S : Set (Q 9))) :
      Fintype.card (SideHigh G T) = (degreeThree G T).card := Fintype.card_coe _
  change ((degreeThree G L).card = 2 ∧ (degreeThree G R).card = 8 ∧
        (degreeTwo G L).card = 10 ∧ (degreeTwo G R).card = 1) ∨
      ((degreeThree G L).card = 4 ∧ (degreeThree G R).card = 6 ∧
        (degreeTwo G L).card = 7 ∧ (degreeTwo G R).card = 4) at hcases
  rcases hcases with ⟨hl, hr, h2l, h2r⟩ | ⟨hl, hr, h2l, h2r⟩
  · exact ⟨b, Or.inl ⟨(hcard L).trans hl, (hcard R).trans hr,
      heL.trans h2r, heR.trans h2l⟩⟩
  · have hfour := (hcard L).trans hl
    have ht := compressed_triangle_free hpart hg
    have hreg := four_edges_on_four_vertices (compressed G L) hfour (heL.trans h2r) ht
    refine ⟨b, Or.inr ⟨two_regular_cycle_of_small_card _ hfour hreg,
      (hcard R).trans hr, heR.trans h2l, ?_⟩⟩
    intro x
    have hd := compressed_degree hpart hdeg (fun hxy hx hy => hlow hxy hx hy) hg x
    rw [hreg x] at hd
    exact Nat.add_left_cancel hd

#print axioms twenty_one_slice_compression

/-- The four square vertices have distinct actual high neighbors on the other
side, and exactly those four vertices lose a degree when their side is compressed. -/
private lemma square_cross_matching
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) (e : cycleGraph 4 ≃g compressed G L)
    (hcount : ∀ x : SideHigh G L, (degreeThree G (G.neighborFinset x.val)).card = 1) :
    ∃ B : Fin 4 ↪ SideHigh G R,
      (∀ i y, G.Adj (e i).val y.val ↔ y = B i) ∧
      ∀ y, (compressed G R).degree y = if y ∈ Set.range B then 2 else 3 := by
  classical
  let N (i : Fin 4) := (univ : Finset (SideHigh G R)).filter (fun y => G.Adj (e i).val y.val)
  have hN (i : Fin 4) : (N i).card = 1 :=
    (side_high_neighbors_card hpart (mem_filter.mp (e i).property).1).trans (hcount (e i))
  choose f hf using fun i => card_eq_one.mp (hN i)
  have hmatch (i : Fin 4) (y : SideHigh G R) : G.Adj (e i).val y.val ↔ y = f i := by
    have hmem : y ∈ N i ↔ G.Adj (e i).val y.val := by simp [N]
    rw [hf i, mem_singleton] at hmem
    exact hmem.symm
  have c4_near : ∀ i j : Fin 4, i ≠ j → (cycleGraph 4).Adj i j ∨
      ∃ k, (cycleGraph 4).Adj i k ∧ (cycleGraph 4).Adj j k := by decide +kernel
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hi := (hmatch i (f i)).mpr rfl
    have hj := (hmatch j (f i)).mpr hij
    have hsep := high_neighbors_compressed_separated hpart.symm hg
      (mem_filter.mp (f i).property).1 (mem_filter.mp (f i).property).2
      hi.symm hj.symm (e.injective.ne hne)
    rcases c4_near i j hne with hadj | ⟨k, hik, hjk⟩
    · exact hsep.1 (e.map_rel_iff.mpr hadj)
    · exact hsep.2 (e k) (e.map_rel_iff.mpr hik) (e.map_rel_iff.mpr hjk)
  let B : Fin 4 ↪ SideHigh G R := ⟨f, hinj⟩
  refine ⟨B, hmatch, ?_⟩
  intro y
  let M := (univ : Finset (SideHigh G L)).filter (fun x => G.Adj y.val x.val)
  have hM := side_high_neighbors_card hpart.symm (mem_filter.mp y.property).1
  change M.card = (degreeThree G (G.neighborFinset y.val)).card at hM
  have hd := compressed_degree hpart.symm hdeg hlow hg y
  rw [← hM] at hd
  by_cases hy : y ∈ Set.range B
  · obtain ⟨i, rfl⟩ := hy
    have hm : M = {e i} := by
      ext x
      have hx : G.Adj (e (e.symm x)).val (B i).val ↔ B i = f (e.symm x) :=
        hmatch (e.symm x) (B i)
      rw [e.apply_symm_apply] at hx
      simp only [M, mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro h
        have he := hinj (hx.mp h.symm)
        rw [he, e.apply_symm_apply]
      · rintro rfl
        exact ((hmatch i (B i)).mpr rfl).symm
    rw [hm, card_singleton] at hd
    rw [ite_eq_left (show B i ∈ Set.range B from ⟨i, rfl⟩)]
    omega
  · have hm : M = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h := (mem_filter.mp hx).2
      have he : y = B (e.symm x) := by
        apply (hmatch (e.symm x) y).mp
        rw [e.apply_symm_apply]
        exact h.symm
      exact hy ⟨e.symm x, he.symm⟩
    rw [hm, card_empty] at hd
    rw [ite_eq_right hy]
    omega

#print axioms square_cross_matching

/-- The larger compressed side must contain an edge between two of the matched
ends. An independent set of four ends would overload the other two vertices. -/
private lemma matched_ends_have_edge
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hV : Fintype.card V = 6) (B : Fin 4 ↪ V)
    (hdeg : ∀ y, H.degree y = if y ∈ Set.range B then 2 else 3) :
    ∃ i j, H.Adj (B i) (B j) := by
  classical
  by_contra! hnone
  let X : Finset V := univ.map B
  let Y : Finset V := univ \ X
  have hx (y : V) : y ∈ X ↔ y ∈ Set.range B := by simp [X, Set.mem_range]
  have hx4 : X.card = 4 := by simp [X]
  have hy2 : Y.card = 2 := by
    change ((univ : Finset V) \ X).card = 2
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hV, hx4]
  obtain ⟨u, hu⟩ := card_pos.mp (show 0 < Y.card by omega)
  have hu' : u ∉ Set.range B := by
    intro h
    exact (mem_sdiff.mp hu).2 ((hx u).mpr h)
  have hydeg (i : Fin 4) : H.degree (B i) = 2 := by
    simpa only [ite_eq_left (show B i ∈ Set.range B from ⟨i, rfl⟩)] using hdeg (B i)
  have hN (i : Fin 4) : H.neighborFinset (B i) = Y := by
    apply eq_of_subset_of_card_le
    · intro y hy
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      intro h
      obtain ⟨j, rfl⟩ := (hx y).mp h
      exact hnone i j ((H.mem_neighborFinset _ _).mp hy)
    · rw [H.card_neighborFinset_eq_degree, hydeg, hy2]
  have hsub : X ⊆ H.neighborFinset u := by
    intro y hy
    obtain ⟨i, rfl⟩ := (hx y).mp hy
    apply (H.mem_neighborFinset _ _).mpr
    exact ((H.mem_neighborFinset _ _).mp (hN i ▸ hu)).symm
  have hbad := card_le_card hsub
  rw [hx4, H.card_neighborFinset_eq_degree, hdeg u, ite_eq_right hu'] at hbad
  omega

#print axioms matched_ends_have_edge

-- Adjacent square indices would yield two different three-edge paths.
private lemma matched_edge_over_diagonal
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth) (e : cycleGraph 4 ≃g compressed G L)
    (B : Fin 4 ↪ SideHigh G R) (hB : ∀ i, G.Adj (e i).val (B i).val)
    {i j : Fin 4} (hij : (compressed G R).Adj (B i) (B j)) :
    ¬ (cycleGraph 4).Adj i j := by
  intro hadj
  obtain ⟨hi, a, ha2, hia, hja⟩ := e.map_rel_iff.mpr hadj
  obtain ⟨hj, b, hb2, hib, hjb⟩ := hij
  have highL (k : Fin 4) : G.degree (e k).val = 3 := (mem_filter.mp (e k).property).2
  have highR (k : Fin 4) : G.degree (B k).val = 3 := (mem_filter.mp (B k).property).2
  have hL := (mem_filter.mp (e i).property).1
  have hn₁ : (e i).val ≠ (e j).val := fun h => hi (Subtype.ext h)
  have hn₂ : a ≠ (B j).val := by
    intro h
    rw [h, highR] at ha2
    omega
  have hn₃ : (e i).val ≠ b := by
    intro h
    rw [← h, highL] at hb2
    omega
  have hn₄ : (B i).val ≠ (B j).val := fun h => hj (Subtype.ext h)
  have he := three_walk_endpoint_injective hpart hg hL hL
    hia hja.symm (hB j) (hB i) hib hjb.symm hn₁ hn₂ hn₃ hn₄ ⟨rfl, rfl⟩
  rw [he.2.1, highR] at ha2
  omega

/-- With four highs on the smaller side, some diagonal of its compressed square
has matched endpoints joined by an actual low path on the other side. -/
private lemma square_cross_diagonal
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth) (e : cycleGraph 4 ≃g compressed G L)
    (hcount : ∀ x : SideHigh G L, (degreeThree G (G.neighborFinset x.val)).card = 1)
    (hR : Fintype.card (SideHigh G R) = 6) :
    ∃ B : Fin 4 ↪ SideHigh G R,
      (∀ i y, G.Adj (e i).val y.val ↔ y = B i) ∧
      (∀ y, (compressed G R).degree y = if y ∈ Set.range B then 2 else 3) ∧
      ∃ i j, i ≠ j ∧ ¬ (cycleGraph 4).Adj i j ∧ (compressed G R).Adj (B i) (B j) := by
  obtain ⟨B, hB, hdegB⟩ := square_cross_matching hpart hdeg hlow hg e hcount
  obtain ⟨i, j, h⟩ := matched_ends_have_edge (compressed G R) hR B hdegB
  exact ⟨B, hB, hdegB, i, j, B.injective.ne_iff.mp h.ne,
    matched_edge_over_diagonal hpart hg e B (fun k => (hB k (B k)).mpr rfl) h, h⟩

#print axioms square_cross_diagonal

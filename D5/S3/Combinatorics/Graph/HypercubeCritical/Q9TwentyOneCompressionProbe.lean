import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe

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
open private compressed_edge_count from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric
open private paritySide parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private twenty_one_high_parity_split twenty_one_half_slice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private SimpleGraph.cycle_iso_of_connected_degree_le_two from
  D5.S3.Combinatorics.Graph.Brooks.General

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

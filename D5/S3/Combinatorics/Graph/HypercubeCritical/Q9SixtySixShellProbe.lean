import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyExclusionProbe

/-! Bounds on the sixth distance layer of a balanced 66-vertex cubic support. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
attribute [local instance] Classical.propDecidable

open private paritySide parity_union parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private distance_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private balanced_cubic_hamming_two_four from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9FourthLeafSignProbe
open private distance_six_shell_partner_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyExclusionProbe
open private distanceSevenPartners distanceSeven_partner_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe

private lemma sixty_six_distance_six_bound {C : Finset (Q 9)}
    (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    {x : Q 9} (hx : x ∈ C) : (shell C x 6).card ≤ 14 := by
  have hcardC : Fintype.card (C : Set (Q 9)) = 66 := by simpa using hc
  have hparity (b : Bool) : (paritySide C b).card = 33 := by
    have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq (parity_bipartite C)
    simp only [hr.degree_eq, Finset.sum_const, smul_eq_mul] at hs
    have hu := congrArg Finset.card (parity_union C)
    rw [Finset.card_union_of_disjoint (by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact Bool.false_ne_true ((Finset.mem_filter.mp hz).2.symm.trans
        (Finset.mem_filter.mp hz').2)), Finset.card_univ, hcardC] at hu
    cases b <;> omega
  let n (k : ℕ) := (Finset.univ.filter
    (fun y : (C : Set (Q 9)) => hammingDist x y.val = k)).card
  let w (k : ℕ) : ℕ := if k % 2 = 0 then 1 else 0
  have hsum : (∑ k ∈ Finset.range 8, n k * w k) =
      ∑ y : (C : Set (Q 9)), w (hammingDist x y.val) := by
    simpa only [n, Finset.sum_const, smul_eq_mul] using
      Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.range 8)
        (g := fun y : (C : Set (Q 9)) => hammingDist x y.val)
        (fun y _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hd x hx y.val y.property))) w
  have heven : (∑ y : (C : Set (Q 9)), w (hammingDist x y.val)) = 33 := by
    dsimp only [w]
    rw [← Finset.card_filter]
    have heq : (Finset.univ.filter (fun y : (C : Set (Q 9)) =>
        hammingDist x y.val % 2 = 0)) = paritySide C (cubeParity x) := by
      ext y
      simp only [paritySide, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (distance_parity x y.val).trans eq_comm
    rw [heq, hparity]
  have he := hsum.trans heven
  simp only [w, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMod, ite_true,
    Nat.mul_one, Nat.zero_add] at he
  have hzero : 1 ≤ n 0 := Finset.card_pos.mpr
    ⟨⟨x,hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hammingDist_self x⟩⟩
  have h24 : 18 ≤ n 2 + n 4 := balanced_cubic_hamming_two_four hr hb ⟨x,hx⟩
  have h6 : n 6 ≤ 14 := by omega
  have hcard : (shell C x 6).card = n 6 := by
    apply Finset.card_bij
      (fun y hy => (⟨y, (Finset.mem_filter.mp hy).1⟩ : (C : Set (Q 9))))
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
    · intro y _ z _ heq
      exact congrArg Subtype.val heq
    · intro y hy
      exact ⟨y.val, Finset.mem_filter.mpr ⟨y.property, (Finset.mem_filter.mp hy).2⟩, rfl⟩
  exact hcard.le.trans h6

open private unusedDirections unused_card distanceSeven_partner_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9PartnerGraphProbe

private lemma sixty_six_partner_capacity {C : Finset (Q 9)}
    (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    {x : Q 9} (hx : x ∈ C) :
    (shell C x 7).card +
        ((Finset.univ : Finset (unusedDirections C x)).filter
          (fun v => (distanceSevenPartners C x).degree v = 2)).card +
        ((distanceSevenPartners C x).cliqueFinset 3).card ≤ 14 := by
  have h6 := sixty_six_distance_six_bound hc hr hb hd hx
  obtain ⟨sigma, hs⟩ := hb
  have hbound := distance_six_shell_partner_bound hs hr hd hx
  have hcard : (distanceSevenPartners C x).edgeFinset.card = (shell C x 7).card :=
    distanceSeven_partner_card hd x
  rw [← hcard]
  exact hbound.trans h6

#print axioms sixty_six_partner_capacity

open Finset

private lemma triangles_through_degree_four {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = 6)
    {a b : V} (hdeg : G.degree a = 4) (hab : a ≠ b) (hnab : ¬ G.Adj a b) :
    G.edgeFinset.card ≤ (G.cliqueFinset 3).card + 4 + G.degree b := by
  let A := (univ.erase a).erase b
  have hsub : G.neighborFinset a ⊆ A := by
    intro v hv
    have h := (G.mem_neighborFinset a v).mp hv
    refine mem_erase.mpr ⟨fun he => hnab (he ▸ h), ?_⟩
    exact mem_erase.mpr ⟨h.ne.symm, mem_univ _⟩
  have hcard : A.card = 4 := by
    simp [A, card_erase_of_mem, hab.symm, hV]
  have hnb := eq_of_subset_of_card_le hsub
    (by rw [hcard, G.card_neighborFinset_eq_degree, hdeg])
  let I := G.incidenceFinset a ∪ G.incidenceFinset b
  let E := G.edgeFinset \ I
  have hI : I ⊆ G.edgeFinset :=
    union_subset (G.incidenceFinset_subset a) (G.incidenceFinset_subset b)
  have hE : E.card + I.card = G.edgeFinset.card := card_sdiff_add_card_eq_card hI
  have hIcard : I.card ≤ 4 + G.degree b := by
    dsimp only [I]
    calc
      _ ≤ (G.incidenceFinset a).card + (G.incidenceFinset b).card := card_union_le _ _
      _ = _ := by simp [hdeg]
  have hnot {edge : Sym2 V} (he : edge ∈ E) :
      a ∉ edge.toFinset ∧ b ∉ edge.toFinset := by
    have hmem := mem_sdiff.mp he
    constructor
    · intro ha
      apply hmem.2
      apply mem_union_left
      rw [incidenceFinset_eq_filter]
      exact mem_filter.mpr ⟨hmem.1, Sym2.mem_toFinset.mp ha⟩
    · intro hb
      apply hmem.2
      apply mem_union_right
      rw [incidenceFinset_eq_filter]
      exact mem_filter.mpr ⟨hmem.1, Sym2.mem_toFinset.mp hb⟩
  have hTriangles : E.card ≤ (G.cliqueFinset 3).card := by
    refine card_le_card_of_injOn (fun edge => insert a edge.toFinset) ?_ ?_
    · intro edge
      refine Sym2.inductionOn edge ?_
      intro v w he
      have hvw := G.mem_edgeFinset.mp (mem_sdiff.mp he).1
      have havo := hnot he
      have hAdj (u : V) (hu : u ∈ (s(v,w) : Sym2 V).toFinset) : G.Adj a u := by
        apply (G.mem_neighborFinset a u).mp
        rw [hnb]
        refine mem_erase.mpr ⟨fun h => havo.2 (h ▸ hu), ?_⟩
        exact mem_erase.mpr ⟨fun h => havo.1 (h ▸ hu), mem_univ _⟩
      have hpair : (s(v,w) : Sym2 V).toFinset = {v,w} := by
        ext u
        simp [Sym2.mem_toFinset, Sym2.mem_iff]
      have hv := hAdj v (by simp [hpair])
      have hw := hAdj w (by simp [hpair])
      change insert a (s(v,w) : Sym2 V).toFinset ∈ G.cliqueFinset 3
      rw [hpair, mem_cliqueFinset_iff, is3Clique_iff]
      exact ⟨a,v,w,hv,hw,hvw,rfl⟩
    · intro p hp q hq hpq
      have hs : p.toFinset = q.toFinset := by
        have ht := congrArg (fun S : Finset V => S.erase a) hpq
        simpa [erase_insert, (hnot hp).1, (hnot hq).1, erase_eq_of_notMem] using ht
      exact Sym2.ext (fun v => by rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hs])
  omega

private lemma partner_edges_le_eight {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = 6)
    (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 2 ∨ G.degree v = 4)
    (hcap : G.edgeFinset.card + (univ.filter (fun v => G.degree v = 2)).card +
      (G.cliqueFinset 3).card ≤ 14) : G.edgeFinset.card ≤ 8 := by
  let H := univ.filter (fun v => G.degree v = 4)
  let L := univ.filter (fun v => G.degree v = 2)
  let A := univ.filter (fun v => 0 < G.degree v)
  let e := G.edgeFinset.card
  let t := (G.cliqueFinset 3).card
  change e + L.card + t ≤ 14 at hcap
  by_contra! hlarge
  change 8 < e at hlarge
  have hA : H ∪ L = A := by
    ext v
    simp only [H, L, A, mem_union, mem_filter, mem_univ, true_and]
    rcases hdeg v with h | h | h <;> simp [h]
  have hdis : Disjoint H L := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    have h := (mem_filter.mp hv).2
    have h' := (mem_filter.mp hv').2
    omega
  have hcard : H.card + L.card = A.card := by rw [← card_union_of_disjoint hdis, hA]
  have hA6 : A.card ≤ 6 := by
    simpa [hV] using card_le_card (subset_univ A)
  have hsumH : ∑ v ∈ H, G.degree v = 4 * H.card := by
    rw [sum_congr rfl (fun v hv => (mem_filter.mp hv).2)]
    simp [mul_comm, H]
  have hsumL : ∑ v ∈ L, G.degree v = 2 * L.card := by
    rw [sum_congr rfl (fun v hv => (mem_filter.mp hv).2)]
    simp [mul_comm, L]
  have hsumA : ∑ v ∈ A, G.degree v = ∑ v : V, G.degree v := by
    apply sum_subset (filter_subset _ _)
    simp only [mem_univ, mem_filter, true_and, not_lt, Nat.le_zero]
    exact fun _ _ h => h
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [← hsumA, ← hA, sum_union hdis, hsumH, hsumL] at hsum
  change 4 * H.card + 2 * L.card = 2 * e at hsum
  have hH : H.Nonempty := card_pos.mp (by omega)
  by_cases hfull : A.card = 6
  · have hthree : 3 ≤ H.card := by omega
    by_cases h11 : 11 ≤ e
    · obtain ⟨a,ha⟩ := hH
      have hda : G.degree a = 4 := (mem_filter.mp ha).2
      have hmissing : ∃ b, a ≠ b ∧ ¬ G.Adj a b := by
        by_contra! hn
        have hsub : univ.erase a ⊆ G.neighborFinset a := by
          intro b hb
          exact (G.mem_neighborFinset a b).mpr (hn b (mem_erase.mp hb).1.symm)
        have hc := card_le_card hsub
        simp [card_erase_of_mem, G.card_neighborFinset_eq_degree, hda, hV] at hc
      obtain ⟨b,hab,hnab⟩ := hmissing
      have hb : G.degree b ≤ 4 := by rcases hdeg b with h | h | h <;> omega
      have hT := triangles_through_degree_four G hV hda hab hnab
      change e ≤ t + 4 + G.degree b at hT
      omega
    · obtain ⟨b,hb⟩ := card_pos.mp (by omega : 0 < L.card)
      have hdb : G.degree b = 2 := (mem_filter.mp hb).2
      have hmissing : ∃ a ∈ H, ¬ G.Adj b a := by
        by_contra! hn
        have hsub : H ⊆ G.neighborFinset b := fun a ha => (G.mem_neighborFinset b a).mpr (hn a ha)
        have hc := card_le_card hsub
        rw [G.card_neighborFinset_eq_degree, hdb] at hc
        omega
      obtain ⟨a,ha,hnab⟩ := hmissing
      have hda : G.degree a = 4 := (mem_filter.mp ha).2
      have hab : a ≠ b := by intro h; rw [h, hdb] at hda; omega
      have hT := triangles_through_degree_four G hV hda hab (fun h => hnab h.symm)
      change e ≤ t + 4 + G.degree b at hT
      omega
  · have hA5 : A.card = 5 := by omega
    have hmissing : ∃ b, b ∉ A := by
      by_contra! hn
      have hEq : A = univ := eq_univ_of_forall hn
      simp [hEq, hV] at hA5
    obtain ⟨b,hb⟩ := hmissing
    obtain ⟨a,ha⟩ := hH
    have hda : G.degree a = 4 := (mem_filter.mp ha).2
    have hdb : G.degree b = 0 := by simpa [A] using hb
    have hab : a ≠ b := by intro h; rw [h, hdb] at hda; omega
    have hnab : ¬ G.Adj a b := fun h => (G.degree_eq_zero b).mp hdb a h.symm
    have hT := triangles_through_degree_four G hV hda hab hnab
    change e ≤ t + 4 + G.degree b at hT
    omega

private lemma sixty_six_distance_seven_le_eight {C : Finset (Q 9)}
    (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hd : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    {x : Q 9} (hx : x ∈ C) : (shell C x 7).card ≤ 8 := by
  let G := distanceSevenPartners C x
  have hV : Fintype.card (unusedDirections C x) = 6 := by simpa using unused_card hr hx
  have hcard : G.edgeFinset.card = (shell C x 7).card := distanceSeven_partner_card hd x
  have hcap := sixty_six_partner_capacity hc hr hb hd hx
  rw [← hcard] at hcap ⊢
  exact partner_edges_le_eight G hV (distanceSeven_partner_degree hr hb hd hx) hcap

#print axioms sixty_six_distance_seven_le_eight

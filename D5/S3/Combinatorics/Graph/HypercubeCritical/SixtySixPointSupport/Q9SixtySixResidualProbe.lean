/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixResidualProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixResidualProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Describe the six vertices left outside the two disjoint radius-three balls of a putative distance-eight pair. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixShellProbe

/-! The three vertices of opposite parity outside two radius-three balls. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
attribute [local instance] Classical.propDecidable

open private HammingSeven.ball HammingSeven.ball_walk root_data hamming_le_walk from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private second third third_witness from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private paritySide parity_bipartite parity_union from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private second_distance third_distance distance_parity ball_exit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction

private lemma ball_odd_part {C : Finset (Q 9)}
    (r : (C : Set (Q 9))) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    HammingSeven.ball G r ∩ paritySide C (!cubeParity r.val) =
      G.neighborFinset r ∪ third G r := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  have hodd (z : (C : Set (Q 9))) :
      z ∈ paritySide C (!cubeParity r.val) ↔ cubeParity r.val ≠ cubeParity z.val := by
    simp only [paritySide, Finset.mem_filter, Finset.mem_univ, true_and]
    cases cubeParity r.val <;> cases cubeParity z.val <;> decide
  ext z
  rw [Finset.mem_inter, hodd]
  change (z ∈ insert r (second G r) ∪ (G.neighborFinset r ∪ third G r) ∧
      cubeParity r.val ≠ cubeParity z.val) ↔ z ∈ G.neighborFinset r ∪ third G r
  constructor
  · rintro ⟨hz, hp⟩
    rcases Finset.mem_union.mp hz with h | h
    · rcases Finset.mem_insert.mp h with rfl | h
      · exact (hp rfl).elim
      · exact (hp ((distance_parity r.val z.val).mp (by rw [second_distance h]))).elim
    · exact h
  · intro hz
    refine ⟨Finset.mem_union_right _ hz, ?_⟩
    rcases Finset.mem_union.mp hz with h | h
    · exact cubeParity_ne_of_adj ((G.mem_neighborFinset r z).mp h)
    · intro hp
      have hdist := (distance_parity r.val z.val).mpr hp
      rw [third_distance h] at hdist
      contradiction

private lemma ball_odd_part_card {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (r : (C : Set (Q 9))) :
    ((HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) r) ∩
      paritySide C (!cubeParity r.val)).card = 15 := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  have hg := BalancedCubeGirth.eight_le_egirth C hb
  have ht := (root_data (parity_bipartite C) hg hr.degree_eq r).2.1
  have hd : Disjoint (G.neighborFinset r) (third G r) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨_,_,_,_,_,_,_,_,hn⟩ := third_witness hz'
    exact hn hz
  rw [ball_odd_part r, Finset.card_union_of_disjoint hd, G.card_neighborFinset_eq_degree,
    hr.degree_eq, ht]

set_option maxHeartbeats 600000 in
-- Normalizing the induced graph and three nested finsets exceeds the default limit.
private lemma sixty_six_distance_eight_residual {C : Finset (Q 9)} (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (x y : (C : Set (Q 9))) (hxy : hammingDist x.val y.val = 8) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    let R := Finset.univ \ (HammingSeven.ball G x ∪ HammingSeven.ball G y)
    let P := R ∩ paritySide C (cubeParity x.val)
    let T := R ∩ paritySide C (!cubeParity x.val)
    P.card = 19 ∧ T.card = 3 ∧ ∀ z ∈ T, G.neighborFinset z ⊆ P := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let A := HammingSeven.ball G x
  let B := HammingSeven.ball G y
  let R := Finset.univ \ (A ∪ B)
  let E := paritySide C (cubeParity x.val)
  let O := paritySide C (!cubeParity x.val)
  let P := R ∩ E
  let T := R ∩ O
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨p,hp⟩ := HammingSeven.ball_walk hz
    obtain ⟨q,hq⟩ := HammingSeven.ball_walk hz'
    have h := hamming_le_walk (p.append q.reverse)
    simp only [Walk.length_append, Walk.length_reverse] at h
    omega
  have hparity := (distance_parity x.val y.val).mp (by rw [hxy])
  have hg := BalancedCubeGirth.eight_le_egirth C hb
  have hA := (root_data (parity_bipartite C) hg hr.degree_eq x).1
  have hB := (root_data (parity_bipartite C) hg hr.degree_eq y).1
  have hC : Fintype.card (C : Set (Q 9)) = 66 := by simpa using hc
  have hR : R.card = 22 := by
    rw [show R = Finset.univ \ (A ∪ B) from rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_union_of_disjoint hAB, Finset.card_univ, hC, hA, hB]
  have hO : O.card = 33 := by
    have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq (parity_bipartite C)
    simp only [hr.degree_eq, Finset.sum_const, smul_eq_mul] at hs
    have hu := congrArg Finset.card (parity_union C)
    rw [Finset.card_union_of_disjoint (by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact Bool.false_ne_true ((Finset.mem_filter.mp hz).2.symm.trans
        (Finset.mem_filter.mp hz').2)), Finset.card_univ, hC] at hu
    change (paritySide C (!cubeParity x.val)).card = 33
    cases cubeParity x.val <;> simp <;> omega
  have hAO : (A ∩ O).card = 15 := ball_odd_part_card hr hb x
  have hBO : (B ∩ O).card = 15 := by
    change (B ∩ paritySide C (!cubeParity x.val)).card = 15
    rw [hparity]
    exact ball_odd_part_card hr hb y
  have hT : T.card = 3 := by
    have hsplit := Finset.card_sdiff_add_card_inter O (A ∪ B)
    have hs : O \ (A ∪ B) = T := by
      ext v
      simp only [T, R, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and, and_comm]
    have hi : O ∩ (A ∪ B) = (A ∩ O) ∪ (B ∩ O) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    rw [hs, hi, Finset.card_union_of_disjoint
      (hAB.mono Finset.inter_subset_left Finset.inter_subset_left), hAO, hBO, hO] at hsplit
    omega
  have parity_split (v : (C : Set (Q 9))) : v ∈ O ↔ v ∉ E := by
    simp only [O,E,paritySide,Finset.mem_filter,Finset.mem_univ,true_and]
    cases cubeParity x.val <;> cases cubeParity v.val <;> decide
  have hPT : P ∪ T = R := by
    ext v
    simp only [P,T,Finset.mem_union,Finset.mem_inter,parity_split]
    tauto
  have hPTdis : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (parity_split v).mp (Finset.mem_inter.mp hw).2 (Finset.mem_inter.mp hv).2
  have hP : P.card = 19 := by
    have h := congrArg Finset.card hPT
    rw [Finset.card_union_of_disjoint hPTdis, hT, hR] at h
    omega
  refine ⟨hP,hT,?_⟩
  intro z hz v hv
  have hzR := Finset.mem_inter.mp hz
  have hpz := (Finset.mem_filter.mp hzR.2).2
  have hvz : G.Adj v z := ((G.mem_neighborFinset z v).mp hv).symm
  have hvpar : cubeParity v.val = cubeParity x.val := by
    have hne := cubeParity_ne_of_adj hvz
    cases h : cubeParity x.val <;> cases h' : cubeParity v.val <;> simp_all
  have hzOutside := (Finset.mem_sdiff.mp hzR.1).2
  have hvA : v ∉ A := fun h => by
    have ht := third_distance (ball_exit h hvz (fun hzA => hzOutside (Finset.mem_union_left _ hzA)))
    have he := (distance_parity x.val v.val).mpr hvpar.symm
    rw [ht] at he
    contradiction
  have hvB : v ∉ B := fun h => by
    have hzB : z ∉ B := fun hb => hzOutside (Finset.mem_union_right _ hb)
    have ht := third_distance (ball_exit h hvz hzB)
    have he := (distance_parity y.val v.val).mpr (hparity.symm.trans hvpar.symm)
    rw [ht] at he
    contradiction
  have hvR : v ∈ R := Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _, fun h => (Finset.mem_union.mp h).elim hvA hvB⟩
  have hvE : v ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvpar⟩
  exact Finset.mem_inter.mpr ⟨hvR,hvE⟩

#print axioms sixty_six_distance_eight_residual

open Finset

private lemma no_short_cycle_four {V : Type*} {G : SimpleGraph V}
    (hg : (8 : ℕ∞) ≤ G.egirth) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  have hp : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨Walk.IsPath.mk' ?_, by simp [p]⟩
    simp [p, hbc.ne, hbd, hab.ne.symm, hcd.ne, hac.symm, hda.ne]
  have h := hg.trans hp.egirth_le_length
  have hlen : p.length = 4 := by simp [p]
  have hn : 8 ≤ p.length := ENat.natCast_le_natCast.mp h
  omega

private lemma no_short_cycle_six {V : Type*} {G : SimpleGraph V}
    (hg : (8 : ℕ∞) ≤ G.egirth) {a b c d e f : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfa : G.Adj f a)
    (hn : [b, c, d, e, f, a].Nodup) : False := by
  let p : G.Walk a a :=
    .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hef (.cons hfa .nil)))))
  have hp : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    exact ⟨Walk.IsPath.mk' hn, by simp [p]⟩
  have h := hg.trans hp.egirth_le_length
  have hlen : p.length = 6 := by simp [p]
  have hbound : 8 ≤ p.length := ENat.natCast_le_natCast.mp h
  omega

private lemma at_most_two_degree_two_into_three {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hg : (8 : ℕ∞) ≤ G.egirth)
    {P T : Finset V} (hdis : Disjoint P T) (hT : T.card = 3) :
    (P.filter (fun p => (G.neighborFinset p ∩ T).card = 2)).card ≤ 2 := by
  let M := P.filter (fun p => (G.neighborFinset p ∩ T).card = 2)
  let N (p : V) := G.neighborFinset p ∩ T
  have hNsub (p : V) : N p ⊆ T := inter_subset_right
  have hM (p : V) (hp : p ∈ M) : (N p).card = 2 := (mem_filter.mp hp).2
  have hAdj {p t : V} (ht : t ∈ N p) : G.Adj p t :=
    (G.mem_neighborFinset p t).mp (mem_inter.mp ht).1
  have hInj : Set.InjOn N (M : Set V) := by
    intro p hp q hq he
    by_contra hpq
    obtain ⟨u,v,huv,hs⟩ := card_eq_two.mp (hM p hp)
    have hu : u ∈ N p := by rw [hs]; simp
    have hv : v ∈ N p := by rw [hs]; simp
    exact no_short_cycle_four hg (hAdj hu) (hAdj (he ▸ hu)).symm
      (hAdj (he ▸ hv)) (hAdj hv).symm hpq huv
  have hsub : M.image N ⊆ T.powersetCard 2 := by
    intro S hS
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hS
    exact mem_powersetCard.mpr ⟨hNsub p,hM p hp⟩
  by_contra! hlarge
  change 2 < M.card at hlarge
  have hAll : M.image N = T.powersetCard 2 := by
    apply eq_of_subset_of_card_le hsub
    rw [card_image_of_injOn hInj, card_powersetCard, hT]
    exact Nat.succ_le_of_lt hlarge
  obtain ⟨a,b,c,hab,hac,hbc,hTset⟩ := card_eq_three.mp hT
  have exists_pair (s t : V) (hs : s ∈ T) (ht : t ∈ T) (hst : s ≠ t) :
      ∃ p ∈ M, N p = {s,t} := by
    apply mem_image.mp
    rw [hAll, mem_powersetCard]
    refine ⟨?_, card_eq_two.mpr ⟨s,t,hst,rfl⟩⟩
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hs
    · exact ht
  have ha : a ∈ T := by rw [hTset]; simp
  have hb : b ∈ T := by rw [hTset]; simp
  have hc : c ∈ T := by rw [hTset]; simp
  obtain ⟨p,hp,hpN⟩ := exists_pair a b ha hb hab
  obtain ⟨q,hq,hqN⟩ := exists_pair b c hb hc hbc
  obtain ⟨r,hr,hrN⟩ := exists_pair c a hc ha hac.symm
  have hpq : p ≠ q := by
    intro he
    have h : a ∈ N q := by rw [← he,hpN]; simp
    simp [hqN,hab,hac] at h
  have hpr : p ≠ r := by
    intro he
    have h : b ∈ N r := by rw [← he,hpN]; simp
    simp [hrN,hbc,hab.symm] at h
  have hqr : q ≠ r := by
    intro he
    have h : b ∈ N r := by rw [← he,hqN]; simp
    simp [hrN,hbc,hab.symm] at h
  have apart {u v : V} (hu : u ∈ M) (hv : v ∈ T) : u ≠ v :=
    fun he => Finset.disjoint_left.mp hdis (mem_filter.mp hu).1 (he ▸ hv)
  have hpa : G.Adj p a := hAdj (by rw [hpN]; simp)
  have hpb : G.Adj p b := hAdj (by rw [hpN]; simp)
  have hqb : G.Adj q b := hAdj (by rw [hqN]; simp)
  have hqc : G.Adj q c := hAdj (by rw [hqN]; simp)
  have hrc : G.Adj r c := hAdj (by rw [hrN]; simp)
  have hra : G.Adj r a := hAdj (by rw [hrN]; simp)
  apply no_short_cycle_six hg hpb hqb.symm hqc hrc.symm hra hpa.symm
  simp [hab, hac, hbc, hpq, hpr, hqr, Ne.symm,
    apart hp ha, apart hp hb, apart hp hc,
    apart hq ha, apart hq hb, apart hq hc,
    apart hr ha, apart hr hb, apart hr hc]

#print axioms at_most_two_degree_two_into_three

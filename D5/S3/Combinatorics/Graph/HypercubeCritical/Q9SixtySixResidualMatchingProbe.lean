/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/Q9SixtySixResidualMatchingProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/Q9SixtySixResidualMatchingProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Charge isolated crossing incidences to the degree-two vertices of the residual graph. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixResidualHalfProbe

/-! Charge isolated residual endpoints of coordinate edges to degree-two vertices. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph Finset
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced flip)
attribute [local instance] Classical.propDecidable

open private HammingSeven.ball HammingSeven.ball_walk root_data hamming_le_walk from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private third from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private ball_exit third_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff diff_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private actual_full_leaf_blocking from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9FourthLeafSignProbe
open private no_cross_between_distant_balls from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyDiameterUpperProbe
open private no_two_ball_attachments_in_opposite_half from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixResidualHalfProbe

private lemma crossing_neighbor {u v : Q 9} (h : (hypercube 9).Adj u v)
    {k : Fin 9} (hk : v k ≠ u k) : v = flip u k := by
  obtain ⟨j,hj⟩ := adjacent_exists_flip h
  have hjk : j = k := by
    by_contra hn
    apply hk
    rw [hj]
    simp [BalancedCriticalSpectrum.flip,Ne.symm hn]
  simpa [hjk] using hj

set_option maxHeartbeats 700000 in
-- The exterior and attachment filters use the same induced graph at several types.
private lemma isolated_crossing_has_degree_two_charge {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (x y w z : (C : Set (Q 9))) (hxy : hammingDist x.val y.val = 8)
    (k : Fin 9) (hk : x.val k = y.val k)
    (hwbit : w.val k = x.val k) (hzbit : z.val k ≠ x.val k) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    let A := HammingSeven.ball G x
    let B := HammingSeven.ball G y
    let R := univ \ (A ∪ B)
    w ∈ R → (G.neighborFinset w ∩ R).card = 0 → z ∈ A → G.Adj z w →
    ∃ a ∈ R, a.val k ≠ x.val k ∧ (G.neighborFinset a ∩ R).card = 2 ∧
      G.Adj z a ∧ ∀ v ∈ A ∪ B, G.Adj v a → v = z := by
  dsimp only
  intro hw hzero hz hzw
  let G := (hypercube 9).induce (C : Set (Q 9))
  let A := HammingSeven.ball G x
  let B := HammingSeven.ball G y
  let R := univ \ (A ∪ B)
  change w ∈ R at hw
  change z ∈ A at hz
  change (G.neighborFinset w ∩ R).card = 0 at hzero
  have hwA : w ∉ A := fun h => (mem_sdiff.mp hw).2 (mem_union_left _ h)
  have hzt := ball_exit hz hzw hwA
  have hflip : w.val = flip z.val k := crossing_neighbor hzw (fun h => hzbit (h.symm.trans hwbit))
  have hd : hammingDist w.val x.val ≤ 2 := by
    have hkdiff : k ∈ diff z.val x.val := mem_filter.mpr ⟨mem_univ _,hzbit⟩
    have hzdist := third_distance hzt
    have hd3 : (diff z.val x.val).card = 3 := by
      change hammingDist z.val x.val = 3
      rw [hammingDist_comm]
      exact hzdist
    change (diff w.val x.val).card ≤ 2
    rw [hflip,diff_flip,ite_eq_left hkdiff,card_erase_of_mem hkdiff,hd3]
  have hwcover (v : (C : Set (Q 9))) (hv : G.Adj v w) : v ∈ A := by
    have hvAB : v ∈ A ∪ B := by
      by_contra hn
      have hp : 0 < (G.neighborFinset w ∩ R).card := card_pos.mpr ⟨v,mem_inter.mpr
        ⟨(G.mem_neighborFinset w v).mpr hv.symm,mem_sdiff.mpr ⟨mem_univ _,hn⟩⟩⟩
      omega
    rcases mem_union.mp hvAB with hvA | hvB
    · exact hvA
    · obtain ⟨p,hp⟩ := HammingSeven.ball_walk hvB
      have h := hamming_le_walk (p.append (.cons hv .nil))
      simp only [Walk.length_append,Walk.length_cons,Walk.length_nil] at h
      have htri := hammingDist_triangle y.val w.val x.val
      rw [hammingDist_comm y.val x.val,hxy] at htri
      omega
  have hfull : ((third G x).filter (fun v => G.Adj v w)).card = 3 := by
    have heq : (third G x).filter (fun v => G.Adj v w) = G.neighborFinset w := by
      ext v
      simp only [mem_filter,G.mem_neighborFinset]
      exact ⟨fun h => h.2.symm, fun h => ⟨ball_exit (hwcover v h.symm) h.symm hwA,h.symm⟩⟩
    rw [heq,G.card_neighborFinset_eq_degree,hr.degree_eq]
  have hN := (root_data (parity_bipartite C)
    (BalancedCubeGirth.eight_le_egirth C hb) hr.degree_eq x).2.2 z hzt
  change (G.neighborFinset z \ A).card = 2 at hN
  obtain ⟨a,ha,haw⟩ := exists_mem_ne (by omega : 1 < (G.neighborFinset z \ A).card) w
  obtain ⟨haN,haA⟩ := mem_sdiff.mp ha
  have hza : G.Adj z a := (G.mem_neighborFinset z a).mp haN
  have haB : a ∉ B := fun h => no_cross_between_distant_balls x y hxy hz h hza
  have haR : a ∈ R := mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_union.mp h).elim haA haB⟩
  have hab : a.val k = z.val k := by
    by_contra h
    exact haw (Subtype.ext ((crossing_neighbor hza h).trans hflip.symm))
  have haBit : a.val k ≠ x.val k := hab ▸ hzbit
  have hone := actual_full_leaf_blocking hr hb x z hzt w hwA a haA hzw hza haw.symm hfull
  have hmissing (v : (C : Set (Q 9))) (hv : v ∈ B) : ¬ G.Adj v a :=
    fun hva => no_two_ball_attachments_in_opposite_half x y a hxy k hk haBit z v hz hza hv hva
  have hsplit : G.neighborFinset a \ R = (third G x).filter (fun v => G.Adj v a) := by
    ext v
    simp only [mem_sdiff,mem_filter,G.mem_neighborFinset]
    constructor
    · rintro ⟨hav,hn⟩
      have hvAB : v ∈ A ∪ B := by
        by_contra h
        exact hn (mem_sdiff.mpr ⟨mem_univ _,h⟩)
      rcases mem_union.mp hvAB with h | h
      · exact ⟨ball_exit h hav.symm haA,hav.symm⟩
      · exact (hmissing v h hav.symm).elim
    · rintro ⟨hvt,hva⟩
      refine ⟨hva.symm, fun hv => (mem_sdiff.mp hv).2 ?_⟩
      exact mem_union_left _ (mem_union_right _ (mem_union_right _ hvt))
  have hdeg := card_sdiff_add_card_inter (G.neighborFinset a) R
  rw [hsplit,hone,G.card_neighborFinset_eq_degree,hr.degree_eq] at hdeg
  have haDeg : (G.neighborFinset a ∩ R).card = 2 := by omega
  refine ⟨a,haR,haBit,haDeg,hza,?_⟩
  intro v hv hva
  have hv' : v ∈ (third G x).filter (fun t => G.Adj t a) := by
    rw [← hsplit]
    exact mem_sdiff.mpr ⟨(G.mem_neighborFinset a v).mpr hva.symm,
      fun h => (mem_sdiff.mp h).2 hv⟩
  have hz' : z ∈ (third G x).filter (fun t => G.Adj t a) := mem_filter.mpr ⟨hzt,hza⟩
  obtain ⟨t,ht⟩ := card_eq_one.mp hone
  rw [ht,mem_singleton] at hv' hz'
  exact hv'.trans hz'.symm

#print axioms isolated_crossing_has_degree_two_charge

set_option maxHeartbeats 900000 in
-- The injection compares two or more dependent copies of the induced graph.
private lemma isolated_crossing_card_le_degree_two {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (x y : (C : Set (Q 9))) (hxy : hammingDist x.val y.val = 8)
    (k : Fin 9) (hk : x.val k = y.val k) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    let B := HammingSeven.ball G x ∪ HammingSeven.ball G y
    let R := univ \ B
    (R.filter (fun w => w.val k = x.val k ∧ (G.neighborFinset w ∩ R).card = 0 ∧
      ∃ z ∈ B, G.Adj z w ∧ z.val k ≠ x.val k)).card ≤
      (R.filter (fun a => a.val k ≠ x.val k ∧ (G.neighborFinset a ∩ R).card = 2)).card := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let B := HammingSeven.ball G x ∪ HammingSeven.ball G y
  let R := univ \ B
  let D := R.filter (fun w => w.val k = x.val k ∧ (G.neighborFinset w ∩ R).card = 0 ∧
    ∃ z ∈ B, G.Adj z w ∧ z.val k ≠ x.val k)
  let T := R.filter (fun a => a.val k ≠ x.val k ∧ (G.neighborFinset a ∩ R).card = 2)
  have charge (w : (C : Set (Q 9))) (hw : w ∈ D) :
      ∃ a ∈ T, ∃ z ∈ B, G.Adj z w ∧ z.val k ≠ x.val k ∧ G.Adj z a ∧
        ∀ v ∈ B, G.Adj v a → v = z := by
    obtain ⟨hwR,hwbit,hw0,z,hz,hzw,hzbit⟩ := mem_filter.mp hw
    rcases mem_union.mp hz with hzX | hzY
    · obtain ⟨a,haR,habit,ha2,hza,hunique⟩ :=
        isolated_crossing_has_degree_two_charge hr hb x y w z hxy k hk
          hwbit hzbit hwR hw0 hzX hzw
      exact ⟨a,mem_filter.mpr ⟨haR,habit,ha2⟩,z,hz,hzw,hzbit,hza,hunique⟩
    · have hyx : hammingDist y.val x.val = 8 := by rw [hammingDist_comm,hxy]
      have hzbit' : z.val k ≠ y.val k := fun h => hzbit (h.trans hk.symm)
      let B' := HammingSeven.ball G y ∪ HammingSeven.ball G x
      have hB' : B' = B := by exact union_comm _ _
      have ha := isolated_crossing_has_degree_two_charge hr hb y x w z hyx k hk.symm
        (hwbit.trans hk) hzbit'
      change w ∈ univ \ B' → (G.neighborFinset w ∩ (univ \ B')).card = 0 →
        z ∈ HammingSeven.ball G y → G.Adj z w →
        ∃ a ∈ univ \ B', a.val k ≠ y.val k ∧ (G.neighborFinset a ∩ (univ \ B')).card = 2 ∧
          G.Adj z a ∧ ∀ v ∈ B', G.Adj v a → v = z at ha
      rw [hB'] at ha
      obtain ⟨a,haR,habit,ha2,hza,hunique⟩ := ha hwR hw0 hzY hzw
      exact ⟨a,mem_filter.mpr ⟨haR,fun h => habit (h.trans hk),ha2⟩,
        z,hz,hzw,hzbit,hza,hunique⟩
  let selectCharge (w : (C : Set (Q 9))) (hw : w ∈ D) := (charge w hw).choose
  change D.card ≤ T.card
  apply card_le_card_of_injOn (fun w => if hw : w ∈ D then selectCharge w hw else x)
  · intro w hw
    change w ∈ D at hw
    simp only [dite_eq_left hw]
    exact (charge w hw).choose_spec.1
  · intro w hw w' hw' he
    change w ∈ D at hw
    change w' ∈ D at hw'
    simp only [dite_eq_left hw,dite_eq_left hw'] at he
    obtain ⟨z,hz,hzw,hzbit,hza,honly⟩ := (charge w hw).choose_spec.2
    obtain ⟨z',hz',hz'w',_,hz'a,_⟩ := (charge w' hw').choose_spec.2
    change G.Adj z' (selectCharge w' hw') at hz'a
    rw [← he] at hz'a
    have hsame : z' = z := honly z' hz' hz'a
    have hwbit := (mem_filter.mp hw).2.1
    have hwbit' := (mem_filter.mp hw').2.1
    apply Subtype.ext
    have hkw : w.val k ≠ z.val k := fun h => hzbit (h.symm.trans hwbit)
    have hkw' : w'.val k ≠ z.val k := fun h => hzbit (h.symm.trans hwbit')
    rw [hsame] at hz'w'
    exact (crossing_neighbor hzw hkw).trans (crossing_neighbor hz'w' hkw').symm

#print axioms isolated_crossing_card_le_degree_two

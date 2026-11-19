/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixResidualHalfProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixResidualHalfProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Constrain the locations and degrees of the six residual vertices in the common-coordinate halves. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixResidualProbe

/-! Attachment restrictions in the coordinate half opposite a distance-eight pair. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph
open Finset
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced)
attribute [local instance] Classical.propDecidable

open private HammingSeven.ball HammingSeven.ball_walk HammingSeven.third_subset_ball
  hamming_le_walk from D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private third from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private agree_of_near_geodesic ball_exit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private full_leaf_other_attachment_in_same_half no_cross_between_distant_balls from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyDiameterUpperProbe

private lemma no_two_ball_attachments_in_opposite_half {C : Finset (Q 9)}
    (x y w : (C : Set (Q 9))) (hxy : hammingDist x.val y.val = 8)
    (k : Fin 9) (hk : x.val k = y.val k) (hw : w.val k ≠ x.val k)
    (u v : (C : Set (Q 9))) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    u ∈ HammingSeven.ball G x → G.Adj u w →
    v ∈ HammingSeven.ball G y → G.Adj v w → False := by
  dsimp only
  intro hu huw hv hvw
  obtain ⟨p,hp⟩ := HammingSeven.ball_walk hu
  obtain ⟨q,hq⟩ := HammingSeven.ball_walk hv
  have hx := hamming_le_walk (p.append (.cons huw .nil))
  have hy := hamming_le_walk (q.append (.cons hvw .nil))
  simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at hx hy
  exact hw (agree_of_near_geodesic hxy (by omega) k hk)

set_option maxHeartbeats 500000 in
-- The choice and injection involve intersections of induced-graph neighbor finsets.
private lemma full_exterior_opposite_half_forces_three_residual_degree_two
    {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (x y w : (C : Set (Q 9)))
    (hxy : hammingDist x.val y.val = 8) (k : Fin 9)
    (hk : x.val k = y.val k) (hw : w.val k ≠ x.val k)
    (hout : w ∉ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x)
    (hfull : ((third ((hypercube 9).induce (C : Set (Q 9))) x).filter
      (fun z => (hypercube 9).Adj z.val w.val)).card = 3) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    let R := univ \ (HammingSeven.ball G x ∪ HammingSeven.ball G y)
    3 ≤ (R.filter (fun a => a.val k ≠ x.val k ∧ (G.neighborFinset a ∩ R).card = 2)).card := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let A := HammingSeven.ball G x
  let B := HammingSeven.ball G y
  let R := univ \ (A ∪ B)
  let L := (third G x).filter (fun z => (hypercube 9).Adj z.val w.val)
  have hlocal (z : (C : Set (Q 9))) (hz : z ∈ L) :
      ∃ a ∈ R, G.Adj z a ∧ a.val k ≠ x.val k ∧
        (G.neighborFinset a ∩ R).card = 2 ∧
        (∀ v ∈ L, G.Adj v a → v = z) := by
    obtain ⟨hzt,hzw⟩ := mem_filter.mp hz
    obtain ⟨a,haA,hza,hbit,hone⟩ :=
      full_leaf_other_attachment_in_same_half hr hb x w k hw hout hfull z hzt hzw
    have hzA : z ∈ A := HammingSeven.third_subset_ball _ hzt
    have haB : a ∉ B :=
      fun ht => no_cross_between_distant_balls x y hxy hzA ht hza
    have haR : a ∈ R := mem_sdiff.mpr ⟨mem_univ _, fun ht => (mem_union.mp ht).elim haA haB⟩
    have hav (v : (C : Set (Q 9))) (hv : v ∈ B) : ¬ G.Adj v a :=
      fun hva => no_two_ball_attachments_in_opposite_half x y a hxy k hk
        (hbit ▸ hw) z v hzA hza hv hva
    have hsplit : G.neighborFinset a \ R = (third G x).filter (fun v => G.Adj v a) := by
      ext v
      simp only [mem_sdiff, mem_filter, G.mem_neighborFinset]
      constructor
      · rintro ⟨hav',hnotR⟩
        have hvAB : v ∈ A ∪ B := by
          by_contra hn
          exact hnotR (mem_sdiff.mpr ⟨mem_univ _,hn⟩)
        rcases mem_union.mp hvAB with hvA | hvB
        · exact ⟨ball_exit hvA hav'.symm haA,hav'.symm⟩
        · exact (hav v hvB hav'.symm).elim
      · rintro ⟨hvt,hva⟩
        refine ⟨hva.symm,fun hv => ?_⟩
        exact (mem_sdiff.mp hv).2 (mem_union_left _ (HammingSeven.third_subset_ball _ hvt))
    have hdeg := card_sdiff_add_card_inter (G.neighborFinset a) R
    rw [hsplit, hone, G.card_neighborFinset_eq_degree, hr.degree_eq] at hdeg
    refine ⟨a,haR,hza,hbit ▸ hw,by omega,?_⟩
    intro v hv hva
    have hz' : z ∈ (third G x).filter (fun t => G.Adj t a) := mem_filter.mpr ⟨hzt,hza⟩
    have hv' : v ∈ (third G x).filter (fun t => G.Adj t a) := mem_filter.mpr
      ⟨(mem_filter.mp hv).1,hva⟩
    obtain ⟨t,ht⟩ := card_eq_one.mp hone
    rw [ht, mem_singleton] at hz' hv'
    exact hv'.trans hz'.symm
  let chooseOther (z : (C : Set (Q 9))) (hz : z ∈ L) := (hlocal z hz).choose
  change 3 ≤ (R.filter _).card
  rw [← hfull]
  change L.card ≤ _
  apply card_le_card_of_injOn (fun z => if hz : z ∈ L then chooseOther z hz else w)
  · intro z hz
    change z ∈ L at hz
    simp only [dite_eq_left hz]
    have ha := (hlocal z hz).choose_spec
    exact mem_filter.mpr ⟨ha.1,ha.2.2.1,ha.2.2.2.1⟩
  · intro z hz t ht hEq
    change z ∈ L at hz
    change t ∈ L at ht
    simp only [dite_eq_left hz, dite_eq_left ht] at hEq
    have hadj : G.Adj t (chooseOther t ht) := ((hlocal t ht).choose_spec).2.1
    rw [← hEq] at hadj
    exact (((hlocal z hz).choose_spec).2.2.2.2 t ht hadj).symm

#print axioms full_exterior_opposite_half_forces_three_residual_degree_two

private lemma opposite_half_card_bound
    {half cut residualOpposite insideRoot insideOpposite delta internalInside internalOutside
      enteringOutside enteringInside backToOutside : ℕ}
    (hcount : half + cut + 2 * internalInside = 4 * (insideRoot + insideOpposite) +
      2 * backToOutside)
    (hresidual : internalInside + internalOutside + enteringOutside + enteringInside =
      3 * residualOpposite)
    (hdegree : internalInside + enteringOutside = insideRoot + delta)
    (hcharge : backToOutside ≤ internalOutside + delta)
    (hmatching : enteringOutside + insideOpposite ≤ residualOpposite) :
    half + cut + 2 * (delta + enteringInside) ≤ 10 * residualOpposite := by
  omega

#print axioms opposite_half_card_bound

open private sixty_six_distance_eight_residual at_most_two_degree_two_into_three from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.Q9SixtySixResidualProbe
open private paritySide from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

set_option maxHeartbeats 700000 in
-- The two instances of the local induced graph and its parity classes need normalization.
private lemma residual_degree_two_card_le_two {C : Finset (Q 9)}
    (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (x y : (C : Set (Q 9)))
    (hxy : hammingDist x.val y.val = 8) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    let R := univ \ (HammingSeven.ball G x ∪ HammingSeven.ball G y)
    (R.filter (fun a => (G.neighborFinset a ∩ R).card = 2)).card ≤ 2 := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let R := univ \ (HammingSeven.ball G x ∪ HammingSeven.ball G y)
  let P := R ∩ paritySide C (cubeParity x.val)
  let T := R ∩ paritySide C (!cubeParity x.val)
  obtain ⟨_,hT,hn⟩ := sixty_six_distance_eight_residual hc hr hb x y hxy
  change T.card = 3 at hT
  change ∀ z ∈ T, G.neighborFinset z ⊆ P at hn
  have hpar (a : (C : Set (Q 9))) :
      cubeParity a.val ≠ cubeParity x.val ↔ cubeParity a.val = !cubeParity x.val := by
    cases cubeParity x.val <;> cases cubeParity a.val <;> decide
  have hdis : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    have hp := (mem_filter.mp (mem_inter.mp ha).2).2
    have ht := (mem_filter.mp (mem_inter.mp ha').2).2
    exact ((hpar a).mpr ht) hp
  have hsubset : R.filter (fun a => (G.neighborFinset a ∩ R).card = 2) ⊆
      P.filter (fun a => (G.neighborFinset a ∩ T).card = 2) := by
    intro a ha
    obtain ⟨haR,ha2⟩ := mem_filter.mp ha
    have haP : cubeParity a.val = cubeParity x.val := by
      by_contra h
      have haT : a ∈ T := mem_inter.mpr ⟨haR,mem_filter.mpr ⟨mem_univ _,(hpar a).mp h⟩⟩
      have hs : G.neighborFinset a ⊆ R := fun v hv => (mem_inter.mp (hn a haT hv)).1
      rw [inter_eq_left.mpr hs, G.card_neighborFinset_eq_degree, hr.degree_eq] at ha2
      omega
    refine mem_filter.mpr ⟨mem_inter.mpr ⟨haR,mem_filter.mpr ⟨mem_univ _,haP⟩⟩,?_⟩
    have heq : G.neighborFinset a ∩ R = G.neighborFinset a ∩ T := by
      ext v
      constructor
      · intro hv
        obtain ⟨hvN,hvR⟩ := mem_inter.mp hv
        have hadj : G.Adj a v := (G.mem_neighborFinset a v).mp hvN
        have hne : cubeParity v.val ≠ cubeParity x.val := by
          rw [← haP]
          exact (cubeParity_ne_of_adj hadj).symm
        exact mem_inter.mpr ⟨hvN,mem_inter.mpr
          ⟨hvR,mem_filter.mpr ⟨mem_univ _,(hpar v).mp hne⟩⟩⟩
      · intro hv
        obtain ⟨hvN,hvT⟩ := mem_inter.mp hv
        exact mem_inter.mpr ⟨hvN,(mem_inter.mp hvT).1⟩
    rwa [heq] at ha2
  exact (card_le_card hsubset).trans
    (at_most_two_degree_two_into_three (BalancedCubeGirth.eight_le_egirth C hb) hdis hT)

set_option maxHeartbeats 600000 in
-- The degree and opposite-half filters contain reducible induced-graph expressions.
private lemma residual_opposite_half_has_no_isolated {C : Finset (Q 9)}
    (hc : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (x y : (C : Set (Q 9))) (hxy : hammingDist x.val y.val = 8)
    (k : Fin 9) (hk : x.val k = y.val k) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    let R := univ \ (HammingSeven.ball G x ∪ HammingSeven.ball G y)
    ∀ w ∈ R, w.val k ≠ x.val k → 0 < (G.neighborFinset w ∩ R).card := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let A := HammingSeven.ball G x
  let B := HammingSeven.ball G y
  let R := univ \ (A ∪ B)
  change ∀ w ∈ R, w.val k ≠ x.val k → 0 < (G.neighborFinset w ∩ R).card
  intro w hw hbit
  by_contra! hzero
  have hAB (v : (C : Set (Q 9))) (hv : G.Adj v w) : v ∈ A ∪ B := by
    by_contra hn
    have hvN : v ∈ G.neighborFinset w := (G.mem_neighborFinset w v).mpr hv.symm
    have hvR : v ∈ R := mem_sdiff.mpr ⟨mem_univ _,hn⟩
    have hp := card_pos.mpr ⟨v,mem_inter.mpr ⟨hvN,hvR⟩⟩
    omega
  have hwA : w ∉ A := fun ha => (mem_sdiff.mp hw).2 (mem_union_left _ ha)
  have hwB : w ∉ B := fun ha => (mem_sdiff.mp hw).2 (mem_union_right _ ha)
  have hfull (r : (C : Set (Q 9))) (hout : w ∉ HammingSeven.ball G r)
      (hcover : ∀ v, G.Adj v w → v ∈ HammingSeven.ball G r) :
      ((third G r).filter (fun z => G.Adj z w)).card = 3 := by
    have heq : (third G r).filter (fun z => G.Adj z w) = G.neighborFinset w := by
      ext v
      simp only [mem_filter,G.mem_neighborFinset]
      exact ⟨fun h => h.2.symm, fun h => ⟨ball_exit (hcover v h.symm) h.symm hout,h.symm⟩⟩
    rw [heq,G.card_neighborFinset_eq_degree,hr.degree_eq]
  have hN : (G.neighborFinset w).card = 3 := by rw [G.card_neighborFinset_eq_degree,hr.degree_eq]
  obtain ⟨u,hu⟩ := card_pos.mp (by omega : 0 < (G.neighborFinset w).card)
  have huw : G.Adj u w := ((G.mem_neighborFinset w u).mp hu).symm
  have bound := residual_degree_two_card_le_two hc hr hb x y hxy
  change (R.filter (fun a => (G.neighborFinset a ∩ R).card = 2)).card ≤ 2 at bound
  rcases mem_union.mp (hAB u huw) with huA | huB
  · have hcover (v : (C : Set (Q 9))) (hv : G.Adj v w) : v ∈ A :=
      (mem_union.mp (hAB v hv)).elim id (fun h =>
        (no_two_ball_attachments_in_opposite_half x y w hxy k hk hbit u v huA huw h hv).elim)
    have hmany := full_exterior_opposite_half_forces_three_residual_degree_two
      hr hb x y w hxy k hk hbit hwA (hfull x hwA hcover)
    have hle : (R.filter (fun a => a.val k ≠ x.val k ∧
          (G.neighborFinset a ∩ R).card = 2)).card ≤
        (R.filter (fun a => (G.neighborFinset a ∩ R).card = 2)).card :=
      card_le_card (fun _ ha => mem_filter.mpr ⟨(mem_filter.mp ha).1,(mem_filter.mp ha).2.2⟩)
    change 3 ≤ (R.filter (fun a => a.val k ≠ x.val k ∧
      (G.neighborFinset a ∩ R).card = 2)).card at hmany
    omega
  · have hcover (v : (C : Set (Q 9))) (hv : G.Adj v w) : v ∈ B :=
      (mem_union.mp (hAB v hv)).elim (fun h =>
        (no_two_ball_attachments_in_opposite_half x y w hxy k hk hbit v u h hv huB huw).elim) id
    have hyx : hammingDist y.val x.val = 8 := by rw [hammingDist_comm,hxy]
    have hbit' : w.val k ≠ y.val k := fun he => hbit (he.trans hk.symm)
    have hmany := full_exterior_opposite_half_forces_three_residual_degree_two
      hr hb y x w hyx k hk.symm hbit' hwB (hfull y hwB hcover)
    let R' := univ \ (B ∪ A)
    change 3 ≤ (R'.filter (fun a => a.val k ≠ y.val k ∧
      (G.neighborFinset a ∩ R').card = 2)).card at hmany
    have hR' : R' = R := by simp only [R',R,union_comm B A]
    rw [hR'] at hmany
    have hle : (R.filter (fun a => a.val k ≠ y.val k ∧
          (G.neighborFinset a ∩ R).card = 2)).card ≤
        (R.filter (fun a => (G.neighborFinset a ∩ R).card = 2)).card :=
      card_le_card (fun _ ha => mem_filter.mpr ⟨(mem_filter.mp ha).1,(mem_filter.mp ha).2.2⟩)
    omega

#print axioms residual_opposite_half_has_no_isolated

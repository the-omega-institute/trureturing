/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyDiameterUpperProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyDiameterUpperProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Use opposite coordinate halves and the fourth-layer counting constraints to rule out distances eight and nine in a sixty-point support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyThinHalfProbe

/-! The geometry of a coordinate half opposite a root in a cubic cube support. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q flip IsBalanced)
attribute [local instance] Classical.propDecidable

open private HammingSeven.ball root_data third_inner_neighbors from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private second third third_witness second_neighbor_inter from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private paritySide parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private second_distance distance_parity from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private word_to_third full_attachment_same_order actual_full_leaf_blocking
  flip_triangle_commute diff_two_flips no_two_steps_to_outside from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9FourthLeafSignProbe
open BalancedCubeGirth (flip_comm)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private diff diff_flip from D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

private lemma ball_subset_has_degree_at_most_one {C : Finset (Q 9)}
    (hb : IsBalanced C) (x : (C : Set (Q 9))) (P : Finset (C : Set (Q 9)))
    (hne : P.Nonempty) (hsub : P ⊆ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x)
    (hx : x ∉ P) :
    ∃ z ∈ P, ((((hypercube 9).induce (C : Set (Q 9))).neighborFinset z) ∩ P).card ≤ 1 := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  have hg := BalancedCubeGirth.eight_le_egirth C hb
  by_cases h₃ : ∃ z ∈ P, z ∈ third G x
  · obtain ⟨z,hz,hzt⟩ := h₃
    have hinner : ((G.neighborFinset z) ∩ HammingSeven.ball G x).card = 1 := by
      cases h : cubeParity x.val
      · exact third_inner_neighbors (parity_bipartite C) hg (by simp [paritySide,h]) hzt
      · exact third_inner_neighbors (parity_bipartite C).symm hg (by simp [paritySide,h]) hzt
    refine ⟨z,hz,?_⟩
    change (G.neighborFinset z ∩ P).card ≤ 1
    apply le_trans (Finset.card_le_card ?_) hinner.le
    intro u hu
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hu).1,hsub (Finset.mem_inter.mp hu).2⟩
  have hcases (z : (C : Set (Q 9))) (hz : z ∈ P) : z ∈ second G x ∨ z ∈ G.neighborFinset x := by
    rcases Finset.mem_union.mp (hsub hz) with h | h
    · rcases Finset.mem_insert.mp h with rfl | h
      · exact (hx hz).elim
      · exact Or.inl h
    · rcases Finset.mem_union.mp h with h | h
      · exact Or.inr h
      · exact (h₃ ⟨z,hz,h⟩).elim
  by_cases h₂ : ∃ z ∈ P, z ∈ second G x
  · obtain ⟨z,hz,hzs⟩ := h₂
    refine ⟨z,hz,?_⟩
    rw [← second_neighbor_inter hg hzs]
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hzw,hwP⟩ := Finset.mem_inter.mp hw
    refine Finset.mem_inter.mpr ⟨hzw,?_⟩
    rcases hcases w hwP with hws | hw₁
    · have hp := cubeParity_ne_of_adj (show G.Adj z w from (G.mem_neighborFinset _ _).mp hzw)
      have hzp := (distance_parity x.val z.val).mp (by rw [second_distance hzs])
      have hwp := (distance_parity x.val w.val).mp (by rw [second_distance hws])
      exact (hp (hzp.symm.trans hwp)).elim
    · exact hw₁
  obtain ⟨z,hz⟩ := hne
  have hall (w : (C : Set (Q 9))) (hw : w ∈ P) : w ∈ G.neighborFinset x := by
    rcases hcases w hw with h | h
    · exact (h₂ ⟨w,hw,h⟩).elim
    · exact h
  have hempty : G.neighborFinset z ∩ P = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hzw,hwP⟩ := Finset.mem_inter.mp hw
    have hzx : cubeParity x.val ≠ cubeParity z.val :=
      cubeParity_ne_of_adj (show G.Adj x z from (G.mem_neighborFinset _ _).mp (hall z hz))
    have hwx : cubeParity x.val ≠ cubeParity w.val :=
      cubeParity_ne_of_adj (show G.Adj x w from (G.mem_neighborFinset _ _).mp (hall w hwP))
    have hsame : cubeParity z.val = cubeParity w.val := by
      cases hx : cubeParity x.val <;> cases hz : cubeParity z.val <;>
        cases hw : cubeParity w.val <;> simp_all
    exact cubeParity_ne_of_adj (show G.Adj z w from (G.mem_neighborFinset _ _).mp hzw) hsame
  refine ⟨z,hz,?_⟩
  change (G.neighborFinset z ∩ P).card ≤ 1
  simp [hempty]

private lemma full_leaf_other_attachment_in_same_half {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (x w : (C : Set (Q 9))) (k : Fin 9)
    (hkw : w.val k ≠ x.val k)
    (hout : w ∉ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x)
    (hfull : ((third ((hypercube 9).induce (C : Set (Q 9))) x).filter
      (fun z => (hypercube 9).Adj z.val w.val)).card = 3)
    (z : (C : Set (Q 9)))
    (hzt : z ∈ third ((hypercube 9).induce (C : Set (Q 9))) x)
    (hzw : (hypercube 9).Adj z.val w.val) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    ∃ a ∉ HammingSeven.ball G x, G.Adj z a ∧ a.val k = w.val k ∧
      ((third G x).filter (fun z => G.Adj z a)).card = 1 := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  obtain ⟨i,p,q,hip,hiq,hpq,hi,hi₂,hzi⟩ := word_to_third hb x z hzt
  have hziC : flip (flip (flip x.val i) p) q ∈ C := hzi ▸ z.property
  have hziw : (hypercube 9).Adj (flip (flip (flip x.val i) p) q) w.val := by
    rw [← hzi]
    exact hzw
  obtain ⟨_,_,hwp,_⟩ := full_attachment_same_order hr hb x w hout hfull
    hip hiq hpq hi hi₂ hziC hziw
  have hpair : k ∈ diff w.val x.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkw⟩
  rw [hwp,diff_two_flips x.val hpq] at hpair
  have hk : k = p ∨ k = q := by simpa [or_comm] using hpair
  have hki : k ≠ i := hk.elim (fun h => h.trans_ne hip.symm) (fun h => h.trans_ne hiq.symm)
  have hzbit : z.val k = w.val k := by
    rw [hzi,flip_triangle_commute x.val i p q,← hwp]
    simp [BalancedCriticalSpectrum.flip,hki]
  obtain ⟨_,_,hdegree⟩ := root_data (parity_bipartite C)
    (BalancedCubeGirth.eight_le_egirth C hb) hr.degree_eq x
  let N := G.neighborFinset z \ HammingSeven.ball G x
  have hN : N.card = 2 := hdegree z hzt
  obtain ⟨a,ha,haw⟩ := Finset.exists_mem_ne (by omega : 1 < N.card) w
  obtain ⟨hza',haout⟩ := Finset.mem_sdiff.mp ha
  have hza : G.Adj z a := (G.mem_neighborFinset _ _).mp hza'
  have habit : a.val k = z.val k := by
    obtain ⟨j,hj⟩ := adjacent_exists_flip (show (hypercube 9).Adj z.val a.val from hza)
    by_cases he : j = k
    · subst j
      exfalso
      apply no_two_steps_to_outside x a haout
      refine ⟨_,hi,BalancedCriticalSpectrum.flip_adj _ _,?_⟩
      rw [hj,hzi]
      rcases hk with h | h
      · rw [h,flip_comm (flip x.val i) p q,BalancedCriticalSpectrum.flip_flip]
        exact BalancedCriticalSpectrum.flip_adj _ _
      · rw [h,BalancedCriticalSpectrum.flip_flip]
        exact BalancedCriticalSpectrum.flip_adj _ _
    · rw [hj]
      simp [BalancedCriticalSpectrum.flip,Ne.symm he]
  refine ⟨a,haout,hza,habit.trans hzbit,?_⟩
  exact actual_full_leaf_blocking hr hb x z hzt w hout a haout hzw hza haw.symm hfull

private lemma full_exterior_forces_single_attachment_in_same_half {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (x w : (C : Set (Q 9))) (k : Fin 9)
    (hkw : w.val k ≠ x.val k)
    (hout : w ∉ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x)
    (hfull : ((third ((hypercube 9).induce (C : Set (Q 9))) x).filter
      (fun z => (hypercube 9).Adj z.val w.val)).card = 3) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    ∃ a ∉ HammingSeven.ball G x, a.val k = w.val k ∧
      ((third G x).filter (fun z => G.Adj z a)).card = 1 := by
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (by rw [hfull]; omega)
  obtain ⟨hzt,hzw⟩ := Finset.mem_filter.mp hz
  obtain ⟨a,ha,_,hbit,hone⟩ :=
    full_leaf_other_attachment_in_same_half hr hb x w k hkw hout hfull z hzt hzw
  exact ⟨a,ha,hbit,hone⟩

#print axioms ball_subset_has_degree_at_most_one
#print axioms full_exterior_forces_single_attachment_in_same_half

open private HammingSeven.ball_walk hamming_le_walk from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HammingSeven
open private first_third_disjoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private parity_union from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private ball_exit agree_of_near_geodesic third_distance from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private half_card_lower_bound_sixty from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyThinHalfProbe

private lemma no_cross_between_distant_balls {C : Finset (Q 9)}
    (x y : (C : Set (Q 9))) (hxy : hammingDist x.val y.val = 8)
    {a b : (C : Set (Q 9))}
    (ha : a ∈ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x)
    (hb : b ∈ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) y) :
    ¬ ((hypercube 9).induce (C : Set (Q 9))).Adj a b := by
  intro hab
  obtain ⟨p,hp⟩ := HammingSeven.ball_walk ha
  obtain ⟨q,hq⟩ := HammingSeven.ball_walk hb
  have h := hamming_le_walk (p.append (.cons hab q.reverse))
  simp only [Walk.length_append, Walk.length_cons, Walk.length_reverse] at h
  omega

private lemma no_opposite_exterior_touch {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (x y : (C : Set (Q 9))) (hxy : hammingDist x.val y.val = 8)
    (k : Fin 9) (hk : x.val k = y.val k)
    (hcover :
      let G := (hypercube 9).induce (C : Set (Q 9))
      ∀ a ∉ HammingSeven.ball G x, a ∉ HammingSeven.ball G y →
        ∀ z, G.Adj z a → z ∈ HammingSeven.ball G x ∨ z ∈ HammingSeven.ball G y)
    (w : (C : Set (Q 9))) (hbit : w.val k ≠ x.val k)
    (hwx : w ∉ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) x)
    (hwy : w ∉ HammingSeven.ball ((hypercube 9).induce (C : Set (Q 9))) y)
    (hhas :
      let G := (hypercube 9).induce (C : Set (Q 9))
      ∃ z ∈ HammingSeven.ball G x, G.Adj z w) : False := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let A := HammingSeven.ball G x
  let B := HammingSeven.ball G y
  have hfullOf (a : (C : Set (Q 9))) (hab : a.val k ≠ x.val k)
      (haA : a ∉ A) (haB : a ∉ B) (ha : ∃ z ∈ A, G.Adj z a) :
      ((third G x).filter (fun z => G.Adj z a)).card = 3 := by
    obtain ⟨z,hz,hza⟩ := ha
    have hd₁ : hammingDist x.val a.val ≤ 4 := by
      obtain ⟨p,hp⟩ := HammingSeven.ball_walk hz
      have h := hamming_le_walk (p.append (.cons hza .nil))
      simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at h
      omega
    have hNeighbors : (third G x).filter (fun z => G.Adj z a) = G.neighborFinset a := by
      ext u
      simp only [Finset.mem_filter, G.mem_neighborFinset]
      constructor
      · exact fun h => h.2.symm
      · intro hau
        refine ⟨ball_exit ?_ hau.symm haA,hau.symm⟩
        rcases hcover a haA haB u hau.symm with hu | hu
        · exact hu
        · exfalso
          apply hab
          obtain ⟨q,hq⟩ := HammingSeven.ball_walk hu
          have h := hamming_le_walk (q.append (.cons hau.symm .nil))
          simp only [Walk.length_append, Walk.length_cons, Walk.length_nil] at h
          exact agree_of_near_geodesic hxy (by omega) k hk
    rw [hNeighbors,G.card_neighborFinset_eq_degree,hr.degree_eq]
  have hwfull := hfullOf w hbit hwx hwy hhas
  obtain ⟨a,haA,haBit,haOne⟩ := full_exterior_forces_single_attachment_in_same_half hr hb
    x w k hbit hwx hwfull
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (by rw [haOne]; decide)
  obtain ⟨hut,hua⟩ := Finset.mem_filter.mp hu
  have huA : u ∈ A := Finset.mem_union_right _ (Finset.mem_union_right _ hut)
  have haB : a ∉ B := fun h => (no_cross_between_distant_balls x y hxy huA h) hua
  have haFull := hfullOf a (fun h => hbit (haBit.symm.trans h)) haA haB ⟨u,huA,hua⟩
  exact (by decide : (1 : ℕ) ≠ 3) (haOne.symm.trans haFull)

private lemma coordinate_half_min_neighbors {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (k : Fin 9) (bit : Bool) (z : (C : Set (Q 9))) (hz : z.val k ≠ bit) :
    let G := (hypercube 9).induce (C : Set (Q 9))
    2 ≤ (G.neighborFinset z ∩ Finset.univ.filter
      (fun a : (C : Set (Q 9)) => a.val k ≠ bit)).card := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  let H := Finset.univ.filter (fun a : (C : Set (Q 9)) => a.val k ≠ bit)
  have hOne : (G.neighborFinset z \ H).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have hflip (a : (C : Set (Q 9))) (ha : a ∈ G.neighborFinset z \ H) :
        a.val = flip z.val k := by
      obtain ⟨haAdj,haH⟩ := Finset.mem_sdiff.mp ha
      have haBit : a.val k = bit := by simpa [H] using haH
      obtain ⟨i,hi⟩ := adjacent_exists_flip
        (show (hypercube 9).Adj z.val a.val from (G.mem_neighborFinset _ _).mp haAdj)
      have hiK : i = k := by
        by_contra hn
        have he : a.val k = z.val k := by
          rw [hi]
          simp [BalancedCriticalSpectrum.flip,Ne.symm hn]
        exact hz (he.symm.trans haBit)
      simpa [hiK] using hi
    exact Subtype.ext ((hflip a ha).trans (hflip b hb).symm)
  have hsum := Finset.card_sdiff_add_card_inter (G.neighborFinset z) H
  rw [G.card_neighborFinset_eq_degree,hr.degree_eq] at hsum
  change 2 ≤ (G.neighborFinset z ∩ H).card
  omega

set_option maxHeartbeats 600000 in
private lemma no_dist_eight_sixty {C : Finset (Q 9)}
    (hc : C.card = 60)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (x y : (C : Set (Q 9))) : hammingDist x.val y.val ≠ 8 := by
  intro hxy
  let G := (hypercube 9).induce (C : Set (Q 9))
  let A := HammingSeven.ball G x
  let B := HammingSeven.ball G y
  have hAb : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨p,hp⟩ := HammingSeven.ball_walk hz
    obtain ⟨q,hq⟩ := HammingSeven.ball_walk hz'
    have h := hamming_le_walk (p.append q.reverse)
    simp only [Walk.length_append, Walk.length_reverse] at h
    omega
  let K := (Finset.univ : Finset (Fin 9)).filter (fun i => x.val i = y.val i)
  have hK : K.card = 1 := by
    have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 9)))
      (fun i => x.val i ≠ y.val i)
    simp only [Finset.card_univ,Fintype.card_fin,not_not] at hh
    change hammingDist x.val y.val + K.card = 9 at hh
    omega
  obtain ⟨k,hkK⟩ := Finset.card_pos.mp (by omega : 0 < K.card)
  have hk := (Finset.mem_filter.mp hkK).2
  let H := Finset.univ.filter (fun z : (C : Set (Q 9)) => z.val k ≠ x.val k)
  let O := paritySide C (!cubeParity x.val)
  let AV := G.neighborFinset x ∪ third G x
  let BV := G.neighborFinset y ∪ third G y
  have hg := BalancedCubeGirth.eight_le_egirth C hb
  obtain ⟨_,hx12,_⟩ := root_data (parity_bipartite C) hg hr.degree_eq x
  obtain ⟨_,hy12,_⟩ := root_data (parity_bipartite C) hg hr.degree_eq y
  have h15 (v : (C : Set (Q 9))) (h12 : (third G v).card = 12) :
      (G.neighborFinset v ∪ third G v).card = 15 := by
    have hdis : Disjoint (G.neighborFinset v) (third G v) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      obtain ⟨_,_,_,_,_,_,_,_,hn⟩ := third_witness hz'
      exact hn hz
    calc
      _ = (G.neighborFinset v).card + (third G v).card :=
        Finset.card_union_of_disjoint hdis
      _ = 15 := by rw [G.card_neighborFinset_eq_degree,hr.degree_eq,h12]
  have hAV : AV.card = 15 := h15 x hx12
  have hBV : BV.card = 15 := h15 y hy12
  have hsubA : AV ⊆ A := fun _ hz => Finset.mem_union_right _ hz
  have hsubB : BV ⊆ B := fun _ hz => Finset.mem_union_right _ hz
  have hO : O.card = 30 := by
    have hs := SimpleGraph.isBipartiteWith_sum_degrees_eq (parity_bipartite C)
    simp only [hr.degree_eq,Finset.sum_const,smul_eq_mul] at hs
    have hu := congrArg Finset.card (parity_union C)
    rw [Finset.card_union_of_disjoint (by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact Bool.false_ne_true ((Finset.mem_filter.mp hz).2.symm.trans
        (Finset.mem_filter.mp hz').2)), Finset.card_univ,
        show Fintype.card (C : Set (Q 9)) = 60 by simpa using hc] at hu
    change (paritySide C (!cubeParity x.val)).card = 30
    cases cubeParity x.val <;> simp <;> omega
  have hxyp := (distance_parity x.val y.val).mp (by rw [hxy])
  have hOdd (u : (C : Set (Q 9))) :
      G.neighborFinset u ∪ third G u ⊆ paritySide C (!cubeParity u.val) := by
    intro z hz
    have hp : cubeParity u.val ≠ cubeParity z.val := by
      rcases Finset.mem_union.mp hz with hz | hz
      · exact cubeParity_ne_of_adj
          (show G.Adj u z from (G.mem_neighborFinset _ _).mp hz)
      · intro he
        have h := (distance_parity u.val z.val).mpr he
        rw [third_distance hz] at h
        contradiction
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    cases h₁ : cubeParity u.val <;> cases h₂ : cubeParity z.val <;> simp_all
  have hOddCovered : AV ∪ BV = O := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset (hOdd x) (by
      simpa only [← hxyp] using hOdd y))
    rw [Finset.card_union_of_disjoint (hAb.mono hsubA hsubB), hAV,hBV,hO]
  have hCover : ∀ a ∉ A, a ∉ B → ∀ z, G.Adj z a → z ∈ A ∨ z ∈ B := by
    intro a haA haB z hza
    have outsideParity (u : (C : Set (Q 9))) (huA : u ∉ A) (huB : u ∉ B) :
        cubeParity u.val = cubeParity x.val := by
      have huO : u ∉ O := by
        rw [← hOddCovered]
        exact fun hu => (Finset.mem_union.mp hu).elim (fun h => huA (hsubA h))
          (fun h => huB (hsubB h))
      cases h : cubeParity x.val <;> cases h' : cubeParity u.val <;> simp_all [O,paritySide]
    by_contra! hn
    exact cubeParity_ne_of_adj hza ((outsideParity z hn.1 hn.2).trans
      (outsideParity a haA haB).symm)
  have hH : H ⊆ A ∪ B := by
    intro w hw
    by_contra h
    have hwA : w ∉ A := fun hA => h (Finset.mem_union_left _ hA)
    have hwB : w ∉ B := fun hB => h (Finset.mem_union_right _ hB)
    have hwbit := (Finset.mem_filter.mp hw).2
    have hN : (G.neighborFinset w).card = 3 := by rw [G.card_neighborFinset_eq_degree,hr.degree_eq]
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset w).card)
    have huw := ((G.mem_neighborFinset _ _).mp hu).symm
    rcases hCover w hwA hwB u huw with huA | huB
    · exact no_opposite_exterior_touch hr hb x y hxy k hk hCover w hwbit hwA hwB ⟨u,huA,huw⟩
    · exact no_opposite_exterior_touch hr hb y x (by rw [hammingDist_comm, hxy]) k hk.symm
        (fun a haB haA z hz => (hCover a haA haB z hz).symm)
        w (fun h' => hwbit (h'.trans hk.symm)) hwB hwA ⟨u,huB,huw⟩
  have hHne : H.Nonempty := by
    have hpos : 0 < (C.filter (fun a => a k = !x.val k)).card :=
      (by decide : 0 < 22).trans_le (half_card_lower_bound_sixty hc hr hb k (!x.val k))
    obtain ⟨a,ha⟩ := Finset.card_pos.mp hpos
    obtain ⟨haC,haK⟩ := Finset.mem_filter.mp ha
    refine ⟨⟨a,haC⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    change a k ≠ x.val k
    rw [haK]
    cases x.val k <;> decide
  have localContradiction (v : (C : Set (Q 9)))
      (P B' : Finset (C : Set (Q 9)))
      (hP : P = H ∩ HammingSeven.ball G v) (hne : P.Nonempty)
      (hv : v.val k = x.val k) (hUnion : H ⊆ HammingSeven.ball G v ∪ B')
      (hNo : ∀ a ∈ HammingSeven.ball G v, ∀ b ∈ B', ¬G.Adj a b) : False := by
    obtain ⟨z,hz,hdeg⟩ := ball_subset_has_degree_at_most_one hb v P hne
      (by rw [hP]; exact Finset.inter_subset_right)
      (by rw [hP]; intro hvp; exact (Finset.mem_filter.mp (Finset.mem_inter.mp hvp).1).2 hv)
    have hz' := Finset.mem_inter.mp (hP ▸ hz)
    have hmin := coordinate_half_min_neighbors hr k (x.val k) z (Finset.mem_filter.mp hz'.1).2
    change 2 ≤ (G.neighborFinset z ∩ H).card at hmin
    have hSub : G.neighborFinset z ∩ H ⊆ G.neighborFinset z ∩ P := by
      intro a ha
      obtain ⟨haN,haH⟩ := Finset.mem_inter.mp ha
      refine Finset.mem_inter.mpr ⟨haN,hP.symm ▸ Finset.mem_inter.mpr ⟨haH,?_⟩⟩
      rcases Finset.mem_union.mp (hUnion haH) with h | h
      · exact h
      · exact (hNo z hz'.2 a h ((G.mem_neighborFinset _ _).mp haN)).elim
    have hh := Finset.card_le_card hSub
    change (G.neighborFinset z ∩ P).card ≤ 1 at hdeg
    omega
  obtain ⟨v,hv⟩ := hHne
  rcases Finset.mem_union.mp (hH hv) with hva | hvb
  · exact localContradiction x (H ∩ A) B rfl ⟨v,Finset.mem_inter.mpr ⟨hv,hva⟩⟩
      rfl hH (fun a ha b hb' => no_cross_between_distant_balls x y hxy ha hb')
  · exact localContradiction y (H ∩ B) A rfl ⟨v,Finset.mem_inter.mpr ⟨hv,hvb⟩⟩
      hk.symm (fun _ ha => Finset.mem_union.mpr ((Finset.mem_union.mp (hH ha)).symm))
      (fun a ha b hb' hab => no_cross_between_distant_balls x y hxy hb' ha hab.symm)

private lemma sixty_diameter_le_seven {C : Finset (Q 9)}
    (hc : C.card = 60)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7 := by
  intro x hx y hy
  have hEight := no_dist_eight_sixty hc hr hb ⟨x,hx⟩ ⟨y,hy⟩
  have hNine : hammingDist x y ≠ 9 := by
    intro h9
    let G := (hypercube 9).induce (C : Set (Q 9))
    let r : (C : Set (Q 9)) := ⟨x,hx⟩
    have hN : (G.neighborFinset r).card = 3 := by rw [G.card_neighborFinset_eq_degree,hr.degree_eq]
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset r).card)
    have hxAdj : (hypercube 9).Adj x u.val := (G.mem_neighborFinset _ _).mp hu
    obtain ⟨k,hk⟩ := adjacent_exists_flip hxAdj
    have hf : diff x y = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_univ,Fintype.card_fin]
      exact h9.ge
    have hku : k ∈ diff x y := by rw [hf]; exact Finset.mem_univ _
    have h8 : hammingDist u.val y = 8 := by
      change (diff u.val y).card = 8
      rw [hk,diff_flip,ite_eq_left hku,Finset.card_erase_of_mem hku]
      change hammingDist x y - 1 = 8
      omega
    exact no_dist_eight_sixty hc hr hb u ⟨y,hy⟩ h8
  have hmax : hammingDist x y ≤ 9 := hammingDist_le_card_fintype
  change hammingDist x y ≠ 8 at hEight
  omega

#print axioms sixty_diameter_le_seven

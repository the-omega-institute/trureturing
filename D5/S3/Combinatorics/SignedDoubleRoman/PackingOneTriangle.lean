/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingOneTriangle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingOneTriangle
   mirror-E: none(waiver:one-triangle-obstruction)
   anchors: []
   utility: none
   digest: A one-triangle edge resolves either ordinarily or by a nine-for-three deletion. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingEdgeInduction
import D5.S3.Combinatorics.SignedDoubleRoman.PackingTwoPairs
import D5.S3.Combinatorics.SignedDoubleRoman.PackingPairUniqueness
import D5.S3.Combinatorics.SignedDoubleRoman.MixedExtensionObstruction

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingOneTriangle

open Finset MixedDefs PackingEdge PackingEdgeInduction PackingInductionCore
open CliqueSaturation PackingPairUniqueness PackingTwoPairs

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1600000 in
/-- A created four-clique forces the two external centres and a clean nine-vertex deletion. -/
theorem one_triangle_obstructed (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V) (u v w a b c : V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hno : C.CliqueFreeOn (S : Set V) 4)
    (hR : ({u, v, w, a, b, c} : Finset V) ⊆ S) (hdist : [u, v, w, a, b].Nodup)
    (hu : C.neighborFinset u ∪ D.neighborFinset u = {v, w, a})
    (hv : C.neighborFinset v ∪ D.neighborFinset v = {u, w, b})
    (hw : C.neighborFinset w ∪ D.neighborFinset w = {u, v, c}) (huv : D.Adj u v)
    (hnoA : ¬ ∃ p q r s t z : V, [p, q, r, s, t, z].Nodup ∧
      ({p, q, r, s, t, z} : Finset V) ⊆ S ∧
      C.Adj p r ∧ C.Adj p s ∧ C.Adj q r ∧ C.Adj q s ∧ C.Adj r s ∧
      (C.Adj t p ∨ D.Adj t p) ∧ (C.Adj t q ∨ D.Adj t q) ∧
      (C.Adj t z ∨ D.Adj t z))
    (K : Finset V) (hK : K ⊆ S \ ({u, v, w, a, b, c} : Finset V))
    (hk : K.card = 4)
    (hclique : (ReducedColour C D {u, v, w, a, b, c} {u, v}
      (S \ {u, v, w, a, b, c})).IsClique (K : Set V)) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  let R : Finset V := {u, v, w, a, b, c}
  let T := S \ R
  let Q : Finset V := {u, v}
  have hP (t : V) : D.neighborFinset t \ R = D.neighborFinset t ∩ T := by
    ext z
    simp only [T, mem_sdiff, mem_inter]
    constructor
    · intro h
      exact ⟨h.1, (hsupport (Or.inr ((D.mem_neighborFinset _ _).mp h.1))).2, h.2⟩
    · intro h
      exact ⟨h.1, h.2.2⟩
  have hNu : C.neighborFinset u ∪ D.neighborFinset u ⊆ R := by
    rw [hu]
    intro z hz
    simp only [R, mem_insert, mem_singleton] at hz ⊢
    tauto
  have hNv : C.neighborFinset v ∪ D.neighborFinset v ⊆ R := by
    rw [hv]
    intro z hz
    simp only [R, mem_insert, mem_singleton] at hz ⊢
    tauto
  have hNw : C.neighborFinset w ∪ D.neighborFinset w ⊆ R := by
    rw [hw]
    intro z hz
    simp only [R, mem_insert, mem_singleton] at hz ⊢
    tauto
  have hb : ∀ t ∈ Q, ∀ z ∈ T, ¬ D.Adj t z := by
    intro t ht z hz htz
    have htzR : z ∈ R := by
      simp only [Q, mem_insert, mem_singleton] at ht
      rcases ht with ht | ht <;> subst t
      · exact hNu (mem_union_right _ ((D.mem_neighborFinset _ _).mpr htz))
      · exact hNv (mem_union_right _ ((D.mem_neighborFinset _ _).mpr htz))
    exact (mem_sdiff.mp hz).2 htzR
  have hcentres : ∀ t ∈ R, ((insert t (D.neighborFinset t)) ∩ Q).card = 1 →
      (D.neighborFinset t ∩ T).card = 2 → t = a ∨ t = b := by
    intro t ht htQ htP
    obtain ⟨htnu, htnv, htedge⟩ := edge_imposing_centre D u v t R
      (subset_union_right.trans hNu) (subset_union_right.trans hNv) htQ (hP t ▸ htP)
    have htnw : t ≠ w := by
      intro h
      subst t
      have hh := sdiff_eq_empty_iff_subset.mpr (subset_union_right.trans hNw)
      rw [← hP w, hh, card_empty] at htP
      omega
    rcases htedge with htu | htv
    · have hh := mem_union_right (C.neighborFinset u)
        ((D.mem_neighborFinset _ _).mpr htu.symm)
      rw [hu] at hh
      simp only [mem_insert, mem_singleton] at hh
      tauto
    · have hh := mem_union_right (C.neighborFinset v)
        ((D.mem_neighborFinset _ _).mpr htv.symm)
      rw [hv] at hh
      simp only [mem_insert, mem_singleton] at hh
      tauto
  have hnot : ¬ C.IsClique (K : Set V) :=
    fun hc => hno (hK.trans sdiff_subset) ((C.isNClique_iff).2 ⟨hc, hk⟩)
  obtain ⟨p, q, hpq', hpqold⟩ := C.not_isClique_iff.mp hnot
  have hp : (p : V) ∈ K := p.property
  have hq : (q : V) ∈ K := q.property
  have hpq : (p : V) ≠ (q : V) := fun h => hpq' (Subtype.ext h)
  obtain ⟨_, r, hrR, hrQ, hrP, hrp, hrq⟩ :=
    (hclique hp hq hpq).2.2.resolve_left hpqold
  have hother : ∃ s ∈ R, ((insert s (D.neighborFinset s)) ∩ Q).card = 1 ∧
      (D.neighborFinset s ∩ T).card = 2 ∧
      ∃ x ∈ K, ∃ y ∈ K, x ≠ y ∧ D.Adj s x ∧ D.Adj s y ∧ s ≠ r := by
    by_contra hh
    have hcentre : ∀ s ∈ R, ((insert s (D.neighborFinset s)) ∩ Q).card = 1 →
        (D.neighborFinset s ∩ T).card = 2 →
        ∀ x ∈ K, ∀ y ∈ K, x ≠ y → D.Adj s x → D.Adj s y → s = r := by
      intro s hs hsQ hsP x hx y hy hxy hsx hsy
      by_contra hsr
      exact hh ⟨s, hs, hsQ, hsP, x, hx, y, hy, hxy, hsx, hsy, hsr⟩
    obtain ⟨x, y, z, t, e, f, hdist', hsub, hxz, hxt, hyz, hyt, hzt,
      hex, hey, hef⟩ := single_centre_obstruction C D S R Q K r
        (by simp [Q, R]) hsupport hno hb hcentre hK hk hclique
    exact hnoA ⟨x, y, z, t, e, f, hdist', hsub, hxz, hxt, hyz, hyt, hzt,
      Or.inr hex, Or.inr hey, Or.inr hef⟩
  obtain ⟨s, hsR, hsQ, hsP, x, hx, y, hy, hxy, hsx, hsy, hsr⟩ := hother
  have hrs : r ≠ s := hsr.symm
  have hra : r = a ∨ r = b := hcentres r hrR hrQ hrP
  have hsa : s = a ∨ s = b := hcentres s hsR hsQ hsP
  have hpair : ({r, s} : Finset V) = {a, b} := by
    rcases hra with hra | hra <;> rcases hsa with hsa | hsa <;> subst r <;> subst s
    · exact (hrs rfl).elim
    · rfl
    · exact pair_comm _ _
    · exact (hrs rfl).elim
  let U : Finset V := {u, v, w}
  have hUab : ∀ t ∈ U, t ≠ a ∧ t ≠ b := by
    intro t ht
    have hdist' := hdist
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      not_false_eq_true, and_true, not_or] at hdist'
    simp only [U, mem_insert, mem_singleton] at ht
    rcases ht with ht | ht | ht <;> subst t <;> aesop
  have hUout : ∀ t ∈ U, t ≠ r ∧ t ≠ s ∧ t ∉ K := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · rcases hra with hra | hra
      · simpa only [hra] using (hUab t ht).1
      · simpa only [hra] using (hUab t ht).2
    · rcases hsa with hsa | hsa
      · simpa only [hsa] using (hUab t ht).1
      · simpa only [hsa] using (hUab t ht).2
    · intro htK
      apply (mem_sdiff.mp (hK htK)).2
      simp only [U, R, mem_insert, mem_singleton] at ht ⊢
      tauto
  have hKout : ∀ t ∈ R, t ∉ K := by
    intro t ht htK
    exact (mem_sdiff.mp (hK htK)).2 ht
  have hcore : ∀ t ∈ R, ((insert t (D.neighborFinset t)) ∩ Q).card = 1 →
      (D.neighborFinset t ∩ T).card = 2 →
      ∃ z ∈ U, D.Adj t z := by
    intro t ht htQ htP
    obtain ⟨htnu, htnv, htedge⟩ := edge_imposing_centre D u v t R
      (subset_union_right.trans hNu) (subset_union_right.trans hNv) htQ (hP t ▸ htP)
    rcases htedge with htu | htv
    · exact ⟨u, by simp [U], htu⟩
    · exact ⟨v, by simp [U], htv⟩
  obtain ⟨cr, hcrU, hrcr⟩ := hcore r hrR hrQ hrP
  obtain ⟨cs, hcsU, hscs⟩ := hcore s hsR hsQ hsP
  have hrD : D.neighborFinset r = insert cr {(p : V), (q : V)} := by
    apply (PackingSaturation.exhaust_colour D C r _ (by
      have hh := hdegree r (hR hrR); omega) (by
        have hpcr : (p : V) ≠ cr := fun h => (hUout cr hcrU).2.2 (h ▸ hp)
        have hqcr : (q : V) ≠ cr := fun h => (hUout cr hcrU).2.2 (h ▸ hq)
        simp [hpq, hpcr.symm, hqcr.symm]) ?_).1
    intro t ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with ht | ht | ht <;> subst t
    · exact hrcr
    · exact hrp
    · exact hrq
  have hsD : D.neighborFinset s = insert cs {x, y} := by
    apply (PackingSaturation.exhaust_colour D C s _ (by
      have hh := hdegree s (hR hsR); omega) (by
        have hxcs : x ≠ cs := fun h => (hUout cs hcsU).2.2 (h ▸ hx)
        have hycs : y ≠ cs := fun h => (hUout cs hcsU).2.2 (h ▸ hy)
        simp [hxy, hxcs.symm, hycs.symm]) ?_).1
    intro t ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with ht | ht | ht <;> subst t
    · exact hscs
    · exact hsx
    · exact hsy
  have hCK : ∀ t ∈ K, C.neighborFinset t ⊆ K := by
    intro t ht z hz
    have hh := (saturated_four_clique C D R Q T K
      (fun t ht => hdegree t (mem_sdiff.mp ht).1) hK hk hclique t ht).2.1
    rw [hh] at hz
    exact (mem_inter.mp hz).2
  have hDK : ∀ t ∈ K, D.neighborFinset t ⊆ {r, s} := by
    intro t ht z hz
    obtain ⟨hzR, hzQ, z', hz', hzz', hzP, _, _⟩ := saturated_imposing_centres C D R Q T K
      (fun t ht => hdegree t (mem_sdiff.mp ht).1) (by
        apply disjoint_left.mpr
        intro z hzT hzR
        exact (mem_sdiff.mp hzT).2 hzR) hK hk hclique
      t ht z ((D.mem_neighborFinset _ _).mp hz)
    have hzcard : (D.neighborFinset z ∩ T).card = 2 := by rw [hzP, card_pair hzz']
    rw [hpair]
    simpa only [mem_insert, mem_singleton] using hcentres z hzR hzQ hzcard
  have hPr : D.neighborFinset r ∩ T = {(p : V), (q : V)} := by
    symm
    apply eq_of_subset_of_card_le
    · intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with ht | ht <;> subst t
      · exact mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hrp, hK hp⟩
      · exact mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hrq, hK hq⟩
    · rw [hrP, card_pair hpq]
  have hPs : D.neighborFinset s ∩ T = {x, y} := by
    symm
    apply eq_of_subset_of_card_le
    · intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with ht | ht <;> subst t
      · exact mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hsx, hK hx⟩
      · exact mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hsy, hK hy⟩
    · rw [hsP, card_pair hxy]
  have hAP : ({x, y} : Finset V) ≠ {(p : V), (q : V)} := by
    intro heq
    apply hrs
    apply saturated_pair_unique C D R Q T K
      (fun t ht => hdegree t (mem_sdiff.mp ht).1) hK hk hclique
      r s p q hrR hsR hp hpq hPr (hPs.trans heq)
  let R2 := K ∪ insert r (insert s U)
  let T2 := S \ R2
  have hR2 : R2 ⊆ S := by
    intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact (mem_sdiff.mp (hK ht)).1
    · simp only [mem_insert] at ht
      rcases ht with ht | ht | ht
      · subst t; exact hR hrR
      · subst t; exact hR hsR
      · exact hR (by simp only [U, R, mem_insert, mem_singleton] at ht ⊢; tauto)
  have hless : T2.card < S.card := by
    have hsplit := card_sdiff_add_card_eq_card hR2
    have hpos : 0 < R2.card := card_pos.mpr ⟨r, by simp [R2]⟩
    dsimp only [T2]
    omega
  let C2 := (C.induce (T2 : Set V)).spanningCoe
  let D2 := (D.induce (T2 : Set V)).spanningCoe
  letI : DecidableRel C2.Adj := Classical.decRel _
  letI : DecidableRel D2.Adj := Classical.decRel _
  obtain ⟨hS2, hdeg2, hno2⟩ := restriction_hypotheses C D S T2 sdiff_subset hdegree hno
  obtain ⟨X, hX, hgood, hsize⟩ := ih T2 hless C2 D2 hS2 hdeg2 hno2
  apply two_pair_reduction C D S K U {x, y} X p q r s cr cs hdegree hsupport
    (hK.trans sdiff_subset) (by
      intro t ht
      apply hR
      simp only [U, R, mem_insert, mem_singleton] at ht ⊢
      tauto)
    (hR hrR) (hR hsR) hk (by exact card_le_three) hp hq hpq
    (hKout r hrR) (hKout s hsR) hrs _ hcrU hcsU _ (card_pair hxy) hAP hrD hsD
    hCK hDK hpqold _ hX hsize hgood
  · apply disjoint_left.mpr
    intro t ht ht'
    simp only [mem_insert] at ht'
    rcases ht' with ht' | ht' | ht'
    · exact (hUout t ht).1 ht'
    · exact (hUout t ht).2.1 ht'
    · exact (hUout t ht).2.2 ht'
  · intro t ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with ht | ht <;> subst t
    · exact hx
    · exact hy
  · intro t ht
    have hlost : ∃ z ∈ U, C.Adj t z ∨ D.Adj t z := by
      simp only [U, mem_insert, mem_singleton] at ht
      rcases ht with ht | ht | ht <;> subst t
      · exact ⟨v, by simp [U], Or.inr huv⟩
      · exact ⟨u, by simp [U], Or.inr huv.symm⟩
      · have hwu : C.Adj w u ∨ D.Adj w u := by
          have hh : u ∈ C.neighborFinset w ∪ D.neighborFinset w := by rw [hw]; simp
          simpa only [mem_union, SimpleGraph.mem_neighborFinset] using hh
        exact ⟨u, by simp [U], hwu⟩
    obtain ⟨z, hz, htz⟩ := hlost
    refine ⟨z, by simp [hz], ?_, htz⟩
    intro hzQ
    simp only [mem_insert, mem_singleton] at hzQ
    rcases hzQ with hzQ | hzQ | hzQ
    · exact (hUout z hz).2.2 (hzQ ▸ hp)
    · exact (hUout z hz).2.2 (hzQ ▸ hq)
    · exact (hUout z hz).2.1 hzQ

/-- A single-triangle domination edge always admits an inductive packing extension. -/
theorem one_triangle_case (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V) (u v w a b c : V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hno : C.CliqueFreeOn (S : Set V) 4)
    (hR : ({u, v, w, a, b, c} : Finset V) ⊆ S) (hdist : [u, v, w, a, b].Nodup)
    (hu : C.neighborFinset u ∪ D.neighborFinset u = {v, w, a})
    (hv : C.neighborFinset v ∪ D.neighborFinset v = {u, w, b})
    (hw : C.neighborFinset w ∪ D.neighborFinset w = {u, v, c}) (huv : D.Adj u v)
    (hnoA : ¬ ∃ p q r s t z : V, [p, q, r, s, t, z].Nodup ∧
      ({p, q, r, s, t, z} : Finset V) ⊆ S ∧
      C.Adj p r ∧ C.Adj p s ∧ C.Adj q r ∧ C.Adj q s ∧ C.Adj r s ∧
      (C.Adj t p ∨ D.Adj t p) ∧ (C.Adj t q ∨ D.Adj t q) ∧
      (C.Adj t z ∨ D.Adj t z)) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  by_cases hres : (ReducedColour C D {u, v, w, a, b, c} {u, v}
      (S \ {u, v, w, a, b, c})).CliqueFreeOn
      ((S \ {u, v, w, a, b, c} : Finset V) : Set V) 4
  · exact regular_one_triangle_case C D S u v w a b c ih hsupport hdegree hR hdist
      hu hv hw huv hres
  · have hres' : ∃ K : Finset V, (K : Set V) ⊆
        (↑(S \ {u, v, w, a, b, c}) : Set V) ∧
        (ReducedColour C D {u, v, w, a, b, c} {u, v}
          (S \ {u, v, w, a, b, c})).IsNClique 4 K := by
      unfold SimpleGraph.CliqueFreeOn at hres
      push_neg at hres
      exact hres
    obtain ⟨K, hK, hknc⟩ := hres'
    obtain ⟨hclique, hk⟩ :=
      (ReducedColour C D {u, v, w, a, b, c} {u, v}
        (S \ {u, v, w, a, b, c})).isNClique_iff.mp hknc
    have hK' : K ⊆ S \ {u, v, w, a, b, c} := by
      intro x hx
      exact hK hx
    exact one_triangle_obstructed C D S u v w a b c ih hsupport hdegree hno hR hdist
      hu hv hw huv hnoA K hK' hk hclique

end D5.S3.Combinatorics.SignedDoubleRoman.PackingOneTriangle

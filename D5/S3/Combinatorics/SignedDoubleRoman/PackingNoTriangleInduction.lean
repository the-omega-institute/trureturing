/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingNoTriangleInduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingNoTriangleInduction
   mirror-E: none(waiver:no-triangle-obstruction-induction)
   anchors: []
   utility: none
   digest: Saturated clique obstructions reduce through their active centres. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingNoTriangleCentres
import D5.S3.Combinatorics.SignedDoubleRoman.PackingThreeInduction
import D5.S3.Combinatorics.SignedDoubleRoman.PackingTwoPairs
import D5.S3.Combinatorics.SignedDoubleRoman.PackingPairUniqueness
import D5.S3.Combinatorics.SignedDoubleRoman.PackingEdgeInduction
import D5.S3.Combinatorics.SignedDoubleRoman.PackingFourInduction

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingNoTriangleInduction

open Finset MixedDefs CliqueSaturation PackingNoTriangleCentres PackingInductionCore

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Classify a created clique by its two, three, or four distinct imposing centres. -/
theorem obstructed_no_triangle_case (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hno : C.CliqueFreeOn (S : Set V) 4)
    (hnoA : ¬ ∃ p q r s c v : V, [p, q, r, s, c, v].Nodup ∧
      ({p, q, r, s, c, v} : Finset V) ⊆ S ∧
      C.Adj p r ∧ C.Adj p s ∧ C.Adj q r ∧ C.Adj q s ∧ C.Adj r s ∧
      (C.Adj c p ∨ D.Adj c p) ∧ (C.Adj c q ∨ D.Adj c q) ∧
      (C.Adj c v ∨ D.Adj c v))
    (u v a b c d : V) (hdist : [u, v, a, b, c, d].Nodup)
    (hR : ({u, v, a, b, c, d} : Finset V) ⊆ S)
    (hu : C.neighborFinset u ∪ D.neighborFinset u = {v, a, b})
    (hv : C.neighborFinset v ∪ D.neighborFinset v = {u, c, d}) (huv : D.Adj u v)
    (K : Finset V) (hK : K ⊆ S \ ({u, v, a, b, c, d} : Finset V))
    (hk : K.card = 4)
    (hclique : (ReducedColour C D ({u, v, a, b, c, d} : Finset V) {u, v}
      (S \ ({u, v, a, b, c, d} : Finset V))).IsClique (K : Set V)) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  let R : Finset V := {u, v, a, b, c, d}
  let Q : Finset V := {u, v}
  let T := S \ R
  let J : Finset V := {a, b, c, d}
  let I := J.filter fun r => ∃ p ∈ K, D.Adj r p
  let P (r : V) := D.neighborFinset r ∩ T
  have hdist' := hdist
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    not_false_eq_true, and_true, not_or] at hdist'
  obtain ⟨⟨huvN, hua, hub, huc, hud⟩, ⟨hva, hvb, hvc, hvd⟩,
    ⟨hab, hac, had⟩, ⟨hbc, hbd⟩, ⟨hcd, _⟩⟩ := hdist'
  have hQ : Q ⊆ R := by simp [Q, R]
  have hJ : J ⊆ R := by
    intro z hz
    simp only [J, R, mem_insert, mem_singleton] at hz ⊢
    tauto
  have hdisj : Disjoint T R := disjoint_left.mpr (fun z hzT hzR =>
    (mem_sdiff.mp hzT).2 hzR)
  have hKout : Disjoint K R := disjoint_left.mpr (fun z hzK hzR =>
    (mem_sdiff.mp (hK hzK)).2 hzR)
  have hboundary : ∀ r ∈ Q, ∀ p ∈ T, ¬D.Adj r p := by
    intro r hr p hp hrp
    have hpR : p ∈ R := by
      rcases mem_insert.mp hr with hru | hr
      · subst r
        have hmem : p ∈ C.neighborFinset u ∪ D.neighborFinset u :=
          mem_union_right _ ((D.mem_neighborFinset _ _).mpr hrp)
        rw [hu] at hmem
        simp only [R, mem_insert, mem_singleton] at hmem ⊢
        tauto
      · have hrv := mem_singleton.mp hr
        subst r
        have hmem : p ∈ C.neighborFinset v ∪ D.neighborFinset v :=
          mem_union_right _ ((D.mem_neighborFinset _ _).mpr hrp)
        rw [hv] at hmem
        simp only [R, mem_insert, mem_singleton] at hmem ⊢
        tauto
    exact (mem_sdiff.mp hp).2 hpR
  have hIfrom (r p : V) (hp : p ∈ K) (hrp : D.Adj r p) : r ∈ I := by
    obtain ⟨hrR, hrnot, _⟩ := centre_data C D S R Q T K hR hQ hdegree hdisj
      sdiff_subset hK hk hclique hboundary r p hp hrp
    have hrJ : r ∈ J := by
      simp only [R, Q, J, mem_insert, mem_singleton, not_or] at hrR hrnot ⊢
      tauto
    exact mem_filter.mpr ⟨hrJ, p, hp, hrp⟩
  have hdata (r : V) (hr : r ∈ I) :
      r ∈ R ∧ r ∉ Q ∧ (P r).card = 2 ∧ P r ⊆ K ∧ C.neighborFinset r = ∅ ∧
      (∀ p ∈ P r, ∀ q ∈ P r, p ≠ q → ¬C.Adj p q) ∧
      ∃ cr ∈ Q, D.neighborFinset r = insert cr (P r) := by
    obtain ⟨_, p, hp, hrp⟩ := mem_filter.mp hr
    exact centre_data C D S R Q T K hR hQ hdegree hdisj
      sdiff_subset hK hk hclique hboundary r p hp hrp
  have hCK : ∀ z ∈ K, C.neighborFinset z ⊆ K := by
    intro z hz t ht
    have he := (saturated_four_clique C D R Q T K
      (fun z hz => hdegree z (mem_sdiff.mp hz).1) hK hk hclique z hz).2.1
    rw [he] at ht
    exact (mem_inter.mp ht).2
  have hDK : ∀ z ∈ K, D.neighborFinset z ⊆ I := by
    intro z hz r hr
    exact hIfrom r z hz ((D.mem_neighborFinset _ _).mp hr).symm
  have hIne : I.Nonempty := by
    have hnot : ¬C.IsClique (K : Set V) := fun h =>
      hno (hK.trans sdiff_subset) ((C.isNClique_iff).2 ⟨h, hk⟩)
    obtain ⟨p, q, hpq, hn⟩ := C.not_isClique_iff.mp hnot
    have hpqn : (p : V) ≠ (q : V) := fun h => hpq (Subtype.ext h)
    obtain ⟨_, r, _, _, _, hrp, _⟩ :=
      (hclique p.property q.property hpqn).2.2.resolve_left hn
    exact ⟨r, hIfrom r p p.property hrp⟩
  have hImin : 2 ≤ I.card := by
    by_contra hle
    have hle' : I.card ≤ 1 := by omega
    obtain ⟨t, ht⟩ := hIne
    have hcentre : ∀ r ∈ R, ((insert r (D.neighborFinset r)) ∩ Q).card = 1 →
        (D.neighborFinset r ∩ T).card = 2 →
        ∀ p ∈ K, ∀ q ∈ K, p ≠ q → D.Adj r p → D.Adj r q → r = t := by
      intro r _ _ _ p hp _ _ _ hrp _
      exact card_le_one.mp hle' r (hIfrom r p hp hrp) t ht
    obtain ⟨p, q, r, s, t, w, hd, hs, hpr, hps, hqr, hqs, hrs, htp, htq, htw⟩ :=
      single_centre_obstruction C D S R Q K t hQ hsupport hno hboundary
        hcentre hK hk hclique
    exact hnoA ⟨p, q, r, s, t, w, hd, hs, hpr, hps, hqr, hqs, hrs,
      Or.inr htp, Or.inr htq, Or.inr htw⟩
  have hImax : I.card ≤ 4 := by
    have hsub : I ⊆ J := filter_subset _ _
    have hJcard : J.card = 4 := by simp [J, hab, hac, had, hbc, hbd, hcd]
    exact (card_le_card hsub).trans (by omega)
  have hPne (r s : V) (hr : r ∈ I) (hs : s ∈ I) (hrs : r ≠ s) : P r ≠ P s := by
    intro he
    obtain ⟨p, q, hpq, hpqeq⟩ := card_eq_two.mp (hdata r hr).2.2.1
    have hp : p ∈ K := (hdata r hr).2.2.2.1 (by rw [hpqeq]; simp)
    exact hrs (PackingPairUniqueness.saturated_pair_unique C D R Q T K
      (fun z hz => hdegree z (mem_sdiff.mp hz).1) hK hk hclique r s p q
      (hdata r hr).1 (hdata s hs).1 hp hpq hpqeq (he.symm.trans hpqeq))
  by_cases hI2 : I.card = 2
  · obtain ⟨r, s, hrs, hIeq⟩ := card_eq_two.mp hI2
    have hr : r ∈ I := by rw [hIeq]; simp
    have hs : s ∈ I := by rw [hIeq]; simp
    obtain ⟨hrR, hrnot, hrPc, hrPK, hCr, hrindep, cr, hcr, hrD⟩ := hdata r hr
    obtain ⟨hsR, hsnot, hsPc, hsPK, hCs, hsindep, cs, hcs, hsD⟩ := hdata s hs
    obtain ⟨p, q, hpq, hpqeq⟩ := card_eq_two.mp hrPc
    have hp : p ∈ K := hrPK (by rw [hpqeq]; simp)
    have hq : q ∈ K := hrPK (by rw [hpqeq]; simp)
    have hrK : r ∉ K := fun h => disjoint_left.mp hKout h hrR
    have hsK : s ∉ K := fun h => disjoint_left.mp hKout h hsR
    have hAP : P s ≠ {p, q} := by
      rw [← hpqeq]
      exact hPne s r hs hr hrs.symm
    let R2 := K ∪ insert r (insert s Q)
    let T2 := S \ R2
    have hR2 : R2 ⊆ S := by
      apply union_subset (hK.trans sdiff_subset)
      exact insert_subset (hR hrR) (insert_subset (hR hsR) (hQ.trans hR))
    have hless : T2.card < S.card := by
      have hh := card_sdiff_add_card_eq_card hR2
      have hn : 0 < R2.card := card_pos.mpr ⟨r, by simp [R2]⟩
      dsimp [T2]
      omega
    let C2 := (C.induce (T2 : Set V)).spanningCoe
    let D2 := (D.induce (T2 : Set V)).spanningCoe
    letI : DecidableRel C2.Adj := Classical.decRel _
    letI : DecidableRel D2.Adj := Classical.decRel _
    obtain ⟨hS2, hd2, hn2⟩ := restriction_hypotheses C D S T2 sdiff_subset hdegree hno
    obtain ⟨X, hX, hg, hsize⟩ := ih T2 hless C2 D2 hS2 hd2 hn2
    have hdis : Disjoint Q (insert r (insert s K)) := by
      apply disjoint_left.mpr
      intro t ht ht'
      rcases mem_insert.mp ht' with htr | ht'
      · exact hrnot (htr ▸ ht)
      rcases mem_insert.mp ht' with hts | htK
      · exact hsnot (hts ▸ ht)
      · exact disjoint_left.mp hKout htK (hQ ht)
    have hDb : ∀ z ∈ K, D.neighborFinset z ⊆ {r, s} := by
      intro z hz
      simpa only [← hIeq] using hDK z hz
    have hpold : ¬C.Adj p q := hrindep p (by rw [hpqeq]; simp)
      q (by rw [hpqeq]; simp) hpq
    rw [hpqeq] at hrD
    apply PackingTwoPairs.two_pair_reduction C D S K Q (P s) X p q r s cr cs
      hdegree hsupport (hK.trans sdiff_subset) (hQ.trans hR) (hR hrR) (hR hsR)
      hk (by dsimp [Q]; exact card_le_two.trans (by omega)) hp hq hpq hrK hsK hrs
      hdis hcr hcs hsPK hsPc hAP hrD hsD hCK hDb hpold _ hX hsize hg
    intro t ht
    have htK : t ∉ K := fun h => disjoint_left.mp hKout h (hQ ht)
    have hts : t ≠ s := fun h => hsnot (h ▸ ht)
    have hnotsel : t ∉ ({p, q, s} : Finset V) := by
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨fun h => htK (h.symm ▸ hp), fun h => htK (h.symm ▸ hq), hts⟩
    rcases mem_insert.mp ht with htu | htv
    · subst t
      refine ⟨v, ?_, ?_, Or.inr huv⟩
      · simp [Q]
      · have hvQ : v ∈ Q := by simp [Q]
        have hvK : v ∉ K := fun h => disjoint_left.mp hKout h (hQ hvQ)
        have hvs : v ≠ s := fun h => hsnot (h ▸ hvQ)
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨fun h => hvK (h.symm ▸ hp), fun h => hvK (h.symm ▸ hq), hvs⟩
    · have htv' := mem_singleton.mp htv
      subst t
      refine ⟨u, ?_, ?_, Or.inr huv.symm⟩
      · simp [Q]
      · have huQ : u ∈ Q := by simp [Q]
        have huK : u ∉ K := fun h => disjoint_left.mp hKout h (hQ huQ)
        have hus : u ≠ s := fun h => hsnot (h ▸ huQ)
        simp only [mem_insert, mem_singleton, not_or]
        exact ⟨fun h => huK (h.symm ▸ hp), fun h => huK (h.symm ▸ hq), hus⟩
  have hcoreu (r : V) (hr : r ∈ I) (hside : r ∈ ({a, b} : Finset V)) :
      D.neighborFinset r = insert u (P r) := by
    obtain ⟨_, _, _, _, _, _, cr, hcr, he⟩ := hdata r hr
    rcases mem_insert.mp hcr with hcr | hcr
    · rwa [hcr] at he
    · have hcrv := mem_singleton.mp hcr
      have hrv : D.Adj r v := (D.mem_neighborFinset _ _).mp (by rw [he, hcrv]; simp)
      have hrN : r ∈ C.neighborFinset v ∪ D.neighborFinset v :=
        mem_union_right _ ((D.mem_neighborFinset _ _).mpr hrv.symm)
      rw [hv] at hrN
      simp only [mem_insert, mem_singleton] at hside hrN
      have hn : r ∉ ({u,c,d} : Finset V) := by
        rcases hside with hr | hr
        · rw [hr]
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨Ne.symm hua, hac, had⟩
        · rw [hr]
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨Ne.symm hub, hbc, hbd⟩
      exact False.elim (hn (by simpa only [mem_insert, mem_singleton] using hrN))
  have hcorev (r : V) (hr : r ∈ I) (hside : r ∈ ({c, d} : Finset V)) :
      D.neighborFinset r = insert v (P r) := by
    obtain ⟨_, _, _, _, _, _, cr, hcr, he⟩ := hdata r hr
    rcases mem_insert.mp hcr with hcr | hcr
    · have hru : D.Adj r u := (D.mem_neighborFinset _ _).mp (by rw [he, hcr]; simp)
      have hrN : r ∈ C.neighborFinset u ∪ D.neighborFinset u :=
        mem_union_right _ ((D.mem_neighborFinset _ _).mpr hru.symm)
      rw [hu] at hrN
      simp only [mem_insert, mem_singleton] at hside hrN
      have hn : r ∉ ({v,a,b} : Finset V) := by
        rcases hside with hr | hr
        · rw [hr]
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨Ne.symm hvc, Ne.symm hac, Ne.symm hbc⟩
        · rw [hr]
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨Ne.symm hvd, Ne.symm had, Ne.symm hbd⟩
      exact False.elim (hn (by simpa only [mem_insert, mem_singleton] using hrN))
    · rwa [mem_singleton.mp hcr] at he
  have hcorefull (x y z w : V) (hNu : C.neighborFinset x ∪ D.neighborFinset x = {y,z,w})
      (hxy : D.Adj x y) (hz : D.neighborFinset z = insert x (P z))
      (hw : D.neighborFinset w = insert x (P w)) : D.neighborFinset x = {y,z,w} := by
    apply Subset.antisymm
    · intro t ht
      rw [← hNu]
      exact mem_union_right _ ht
    · intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with hty | htz | htw
      · subst t
        exact (D.mem_neighborFinset _ _).mpr hxy
      · subst t
        apply (D.mem_neighborFinset _ _).mpr
        exact ((D.mem_neighborFinset _ _).mp (show x ∈ D.neighborFinset z by rw [hz]; simp)).symm
      · subst t
        apply (D.mem_neighborFinset _ _).mpr
        exact ((D.mem_neighborFinset _ _).mp (show x ∈ D.neighborFinset w by rw [hw]; simp)).symm
  have three (u' v' a' b' c' d' : V)
      (hd : [u',v',a',b',c',d'].Nodup)
      (hRe : ({u',v',a',b',c',d'} : Finset V) = R)
      (hIe : I = {a',b',c'})
      (hNu : C.neighborFinset u' ∪ D.neighborFinset u' = {v',a',b'})
      (hNv : C.neighborFinset v' ∪ D.neighborFinset v' = {u',c',d'})
      (hDuv : D.Adj u' v')
      (hDa : D.neighborFinset a' = insert u' (P a'))
      (hDb : D.neighborFinset b' = insert u' (P b'))
      (hDc : D.neighborFinset c' = insert v' (P c')) :
      ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
    have haI : a' ∈ I := by rw [hIe]; simp
    have hbI : b' ∈ I := by rw [hIe]; simp
    have hcI : c' ∈ I := by rw [hIe]; simp
    obtain ⟨p, q, hpq, hpair⟩ := card_eq_two.mp (hdata a' haI).2.2.1
    have hp : p ∈ K := (hdata a' haI).2.2.2.1 (by rw [hpair]; simp)
    have hq : q ∈ K := (hdata a' haI).2.2.2.1 (by rw [hpair]; simp)
    have hnopq := (hdata a' haI).2.2.2.2.2.1 p (by rw [hpair]; simp)
      q (by rw [hpair]; simp) hpq
    have hdk : ∀ r ∈ K, D.neighborFinset r ⊆ {a',b',c'} := by
      intro r hr
      rw [← hIe]
      exact hDK r hr
    have hnd := hd
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      not_false_eq_true, and_true, not_or] at hnd
    have hAP : P b' ≠ {p,q} := by
      rw [← hpair]
      exact hPne b' a' hbI haI (Ne.symm hnd.2.2.1.1)
    have hBP : P c' ≠ {p,q} := by
      rw [← hpair]
      exact hPne c' a' hcI haI (Ne.symm hnd.2.2.1.2.1)
    have hDV : C.Adj d' v' ∨ D.Adj d' v' := by
      have hm : d' ∈ C.neighborFinset v' ∪ D.neighborFinset v' := by rw [hNv]; simp
      have hh : C.Adj v' d' ∨ D.Adj v' d' := by
        simpa only [mem_union, SimpleGraph.mem_neighborFinset] using hm
      exact hh.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    have hDU := hcorefull u' v' a' b' hNu hDuv hDa hDb
    rw [hpair] at hDa
    apply PackingThreeInduction.three_centre_case C D S K (P b') (P c')
      ih hsupport hdegree hno hnoA u' v' a' b' c' d' p q hd hk _ _ hp hq hpq
      (hdata b' hbI).2.2.2.1 (hdata b' hbI).2.2.1 hAP
      (hdata c' hcI).2.2.2.1 (hdata c' hcI).2.2.1 hBP
      hDU hDa hDb hDc hNv hDV hCK hdk hnopq
    · rwa [hRe]
    · rw [hRe]
      exact union_subset (hK.trans sdiff_subset) hR
  by_cases hI3 : I.card = 3
  · have hIc : I ⊆ J := filter_subset _ _
    have hJc : J.card = 4 := by simp [J, hab, hac, had, hbc, hbd, hcd]
    obtain ⟨w, hwJ, hwI⟩ := exists_mem_notMem_of_card_lt_card (by omega : I.card < J.card)
    have hIe : I = J.erase w := by
      apply eq_of_subset_of_card_le
      · exact fun z hz => mem_erase.mpr ⟨fun he => hwI (he ▸ hz), hIc hz⟩
      · rw [card_erase_of_mem hwJ, hJc, hI3]
    simp only [J, mem_insert, mem_singleton] at hwJ
    rcases hwJ with hw | hw | hw | hw
    · subst w
      have he : I = {b,c,d} := by
        have hh := hIe
        simpa [J, erase_insert_of_ne, hab, hac, had, hbc, hbd, hcd, ne_comm] using hh
      have hbI : b ∈ I := by rw [he]; simp
      have hcI : c ∈ I := by rw [he]; simp
      have hdI : d ∈ I := by rw [he]; simp
      exact three v u c d b a (by simp [List.nodup_cons, huvN, hua, hub, huc, hud, hva, hvb,
        hvc, hvd, hab, hac, had, hbc, hbd, hcd, ne_comm])
        (by ext z; simp [R, or_assoc, or_left_comm, or_comm])
        (by rw [he]; ext z; simp [or_assoc, or_left_comm, or_comm])
        hv (by simpa [pair_comm] using hu)
        huv.symm (hcorev c hcI (by simp)) (hcorev d hdI (by simp)) (hcoreu b hbI (by simp))
    · subst w
      have he : I = {a,c,d} := by
        have hh := hIe
        simpa [J, erase_insert_of_ne, hab, hac, had, hbc, hbd, hcd, ne_comm] using hh
      have haI : a ∈ I := by rw [he]; simp
      have hcI : c ∈ I := by rw [he]; simp
      have hdI : d ∈ I := by rw [he]; simp
      exact three v u c d a b (by simp [List.nodup_cons, huvN, hua, hub, huc, hud, hva, hvb,
        hvc, hvd, hab, hac, had, hbc, hbd, hcd, ne_comm])
        (by ext z; simp [R, or_assoc, or_left_comm, or_comm])
        (by rw [he]; ext z; simp [or_assoc, or_left_comm, or_comm])
        hv hu huv.symm (hcorev c hcI (by simp)) (hcorev d hdI (by simp))
        (hcoreu a haI (by simp))
    · subst w
      have he : I = {a,b,d} := by
        have hh := hIe
        simpa [J, erase_insert_of_ne, hab, hac, had, hbc, hbd, hcd, ne_comm] using hh
      have haI : a ∈ I := by rw [he]; simp
      have hbI : b ∈ I := by rw [he]; simp
      have hdI : d ∈ I := by rw [he]; simp
      exact three u v a b d c (by simp [List.nodup_cons, huvN, hua, hub, huc, hud, hva, hvb,
        hvc, hvd, hab, hac, had, hbc, hbd, hcd, ne_comm])
        (by ext z; simp [R, or_assoc, or_left_comm, or_comm]) he
        hu (by simpa [pair_comm] using hv) huv (hcoreu a haI (by simp))
        (hcoreu b hbI (by simp)) (hcorev d hdI (by simp))
    · subst w
      have he : I = {a,b,c} := by
        have hh := hIe
        simpa [J, erase_insert_of_ne, hab, hac, had, hbc, hbd, hcd, ne_comm] using hh
      have haI : a ∈ I := by rw [he]; simp
      have hbI : b ∈ I := by rw [he]; simp
      have hcI : c ∈ I := by rw [he]; simp
      exact three u v a b c d hdist rfl he hu hv huv (hcoreu a haI (by simp))
        (hcoreu b hbI (by simp)) (hcorev c hcI (by simp))
  have hI4 : I.card = 4 := by omega
  have hIe : I = J := eq_of_subset_of_card_le (filter_subset _ _)
    (by simp [J, hab, hac, had, hbc, hbd, hcd, hI4])
  have haI : a ∈ I := by rw [hIe]; simp [J]
  have hbI : b ∈ I := by rw [hIe]; simp [J]
  have hcI : c ∈ I := by rw [hIe]; simp [J]
  have hdI : d ∈ I := by rw [hIe]; simp [J]
  have hDa := hcoreu a haI (by simp)
  have hDb := hcoreu b hbI (by simp)
  have hDc := hcorev c hcI (by simp)
  have hDd := hcorev d hdI (by simp)
  have hDu := hcorefull u v a b hu huv hDa hDb
  have hDv := hcorefull v u c d hv huv.symm hDc hDd
  let A : Finset V := {a,b}
  let B : Finset V := {c,d}
  have hABJ : A ∪ B = J := by ext z; simp [A, B, J, or_assoc, or_left_comm, or_comm]
  have hR4 : insert u (insert v (K ∪ A ∪ B)) ⊆ S := by
    intro z hz
    simp only [mem_insert, mem_union] at hz
    rcases hz with rfl | rfl | (hz | hz) | hz
    · exact hR (by simp)
    · exact hR (by simp)
    · exact (mem_sdiff.mp (hK hz)).1
    · exact hR (hJ (by rw [← hABJ]; exact mem_union_left _ hz))
    · exact hR (hJ (by rw [← hABJ]; exact mem_union_right _ hz))
  have huK : u ∉ K := fun h => disjoint_left.mp hKout h (by simp [R])
  have hvK : v ∉ K := fun h => disjoint_left.mp hKout h (by simp [R])
  have hKA : Disjoint K A := hKout.mono_right (fun z hz =>
    hJ (by rw [← hABJ]; exact mem_union_left _ hz))
  have hKB : Disjoint K B := hKout.mono_right (fun z hz =>
    hJ (by rw [← hABJ]; exact mem_union_right _ hz))
  have hDC : ∀ r ∈ A ∪ B, D.degree r = 3 := by
    intro r hr
    have hrI : r ∈ I := by rw [hIe, ← hABJ]; exact hr
    obtain ⟨_, _, hpc, _, _, _, core, hcore, hDr⟩ := hdata r hrI
    have hcoreT : core ∉ T := fun h => disjoint_left.mp hdisj h (hQ hcore)
    change (D.neighborFinset r).card = 3
    rw [hDr, card_insert_of_notMem (fun h => hcoreT (mem_inter.mp h).2), hpc]
  have hpair : ∀ r ∈ A ∪ B, (D.neighborFinset r ∩ K).card = 2 := by
    intro r hr
    have hrI : r ∈ I := by rw [hIe, ← hABJ]; exact hr
    obtain ⟨_, _, hpc, hpK, _, _, core, hcore, hDr⟩ := hdata r hrI
    have hcoreK : core ∉ K := fun h => disjoint_left.mp hKout h (hQ hcore)
    have heq : D.neighborFinset r ∩ K = P r := by
      rw [hDr]
      ext z
      simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨hz | hz, hzK⟩
        · exact False.elim (hcoreK (hz ▸ hzK))
        · exact hz
      · exact fun hz => ⟨Or.inr hz, hpK hz⟩
    rwa [heq]
  apply PackingFourInduction.four_centre_case C D S K A B u v ih
    hsupport hdegree hno hR4 hk _ _ hKA hKB _ _ _ huv.ne hDu hDv _ _ hDC hpair hCK _
  · simp [A, hab]
  · simp [B, hcd]
  · simp [A, B, Finset.disjoint_left, hac, had, hbc, hbd]
  · simp [A, B, huK, hua, hub, huc, hud]
  · simp [A, B, hvK, hva, hvb, hvc, hvd]
  · intro r hr
    have hrI : r ∈ I := by rw [hIe, ← hABJ]; exact mem_union_left _ hr
    rw [hcoreu r hrI hr]
    exact insert_subset (by simp) (fun z hz => mem_insert_of_mem ((hdata r hrI).2.2.2.1 hz))
  · intro r hr
    have hrI : r ∈ I := by rw [hIe, ← hABJ]; exact mem_union_right _ hr
    rw [hcorev r hrI hr]
    exact insert_subset (by simp) (fun z hz => mem_insert_of_mem ((hdata r hrI).2.2.2.1 hz))
  · intro r hr
    rw [hABJ, ← hIe]
    exact hDK r hr

/-- Triangle-free domination edges either lift directly or resolve a saturated clique. -/
theorem no_triangle_case (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hno : C.CliqueFreeOn (S : Set V) 4)
    (hnoA : ¬ ∃ p q r s c v : V, [p, q, r, s, c, v].Nodup ∧
      ({p, q, r, s, c, v} : Finset V) ⊆ S ∧
      C.Adj p r ∧ C.Adj p s ∧ C.Adj q r ∧ C.Adj q s ∧ C.Adj r s ∧
      (C.Adj c p ∨ D.Adj c p) ∧ (C.Adj c q ∨ D.Adj c q) ∧
      (C.Adj c v ∨ D.Adj c v))
    (u v a b c d : V) (hdist : [u,v,a,b,c,d].Nodup)
    (hR : ({u,v,a,b,c,d} : Finset V) ⊆ S)
    (hu : C.neighborFinset u ∪ D.neighborFinset u = {v,a,b})
    (hv : C.neighborFinset v ∪ D.neighborFinset v = {u,c,d}) (huv : D.Adj u v) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  let R : Finset V := {u,v,a,b,c,d}
  by_cases hres : (ReducedColour C D R {u,v} (S \ R)).CliqueFreeOn
      ((S \ R : Finset V) : Set V) 4
  · exact PackingEdgeInduction.regular_no_triangle_case C D S u v a b c d
      ih hsupport hdegree hR hdist hu hv huv hres
  · have hres' : ∃ K : Finset V, (K : Set V) ⊆ (↑(S \ R) : Set V) ∧
        (ReducedColour C D R {u,v} (S \ R)).IsNClique 4 K := by
      unfold SimpleGraph.CliqueFreeOn at hres
      push_neg at hres
      exact hres
    obtain ⟨K, hK, hknc⟩ := hres'
    obtain ⟨hc, hk⟩ := (ReducedColour C D R {u,v} (S \ R)).isNClique_iff.mp hknc
    have hK' : K ⊆ S \ R := by
      intro x hx
      exact hK hx
    exact obstructed_no_triangle_case C D S ih hsupport hdegree hno hnoA
      u v a b c d hdist hR hu hv huv K hK' hk hc

#print axioms no_triangle_case

end D5.S3.Combinatorics.SignedDoubleRoman.PackingNoTriangleInduction

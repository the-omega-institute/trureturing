/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingTwoPairs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingTwoPairs
   mirror-E: none(waiver:two-pair-obstruction-reduction)
   anchors: []
   utility: none
   digest: Two saturated missing pairs yield three selected vertices without a new constraint. -/

import D5.S3.Combinatorics.SignedDoubleRoman.MixedExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingTwoPairs

open Finset MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The same two-pair lift handles the low-degree, one-triangle, and two-added-edge cases. -/
theorem two_pair_reduction (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    (S K U A X : Finset V) (p q r s cr cs : V)
    (hdegree : DegreeBound C D S) (hsupport : Supported C D S)
    (hK : K ⊆ S) (hU : U ⊆ S) (hrS : r ∈ S) (hsS : s ∈ S)
    (hcard : K.card = 4) (hUcard : U.card ≤ 3)
    (hp : p ∈ K) (hq : q ∈ K) (hpq : p ≠ q)
    (hrK : r ∉ K) (hsK : s ∉ K) (hrs : r ≠ s)
    (hdisj : Disjoint U (insert r (insert s K))) (hcr : cr ∈ U) (hcs : cs ∈ U)
    (hA : A ⊆ K) (hAcard : A.card = 2) (hAP : A ≠ {p, q})
    (hDr : D.neighborFinset r = insert cr {p, q})
    (hDs : D.neighborFinset s = insert cs A)
    (hCK : ∀ v ∈ K, C.neighborFinset v ⊆ K)
    (hDK : ∀ v ∈ K, D.neighborFinset v ⊆ {r, s})
    (hnopq : ¬ C.Adj p q)
    (hlost : ∀ v ∈ U, ∃ y ∈ K ∪ insert r (insert s U),
      y ∉ ({p, q, s} : Finset V) ∧ (C.Adj v y ∨ D.Adj v y))
    (hX : X ⊆ S \ (K ∪ insert r (insert s U)))
    (hsize : (S \ (K ∪ insert r (insert s U))).card ≤ 3 * X.card)
    (hadmissible :
      let T := S \ (K ∪ insert r (insert s U))
      let C' := (C.induce (T : Set V)).spanningCoe
      let D' := (D.induce (T : Set V)).spanningCoe
      letI := Classical.decRel D'.Adj
      MixedAdmissible C' D' X) :
    ∃ Y : Finset V, Y ⊆ S ∧ MixedAdmissible C D Y ∧ S.card ≤ 3 * Y.card := by
  classical
  let R := K ∪ insert r (insert s U)
  let Q : Finset V := {p, q, s}
  let T := S \ R
  have hR : R ⊆ S := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · exact hK hv
    · rcases mem_insert.mp hv with rfl | hv
      · exact hrS
      · rcases mem_insert.mp hv with rfl | hv
        · exact hsS
        · exact hU hv
  have hQ : Q ⊆ R := by
    intro v hv
    simp only [Q, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact mem_union_left _ hp
    · exact mem_union_left _ hq
    · simp [R]
  have hrp : r ≠ p := fun h => hrK (h.symm ▸ hp)
  have hrq : r ≠ q := fun h => hrK (h.symm ▸ hq)
  have hrQ : r ∉ Q := by simp [Q, hrp, hrq, hrs]
  have hUout : ∀ v ∈ U, v ≠ r ∧ v ≠ s ∧ v ∉ K := by
    intro v hv
    have hh := disjoint_left.mp hdisj hv
    constructor
    · intro h
      exact hh (by simp [h])
    · constructor
      · intro h
        exact hh (by simp [h])
      · intro h
        exact hh (by simp [h])
  have hUnQ : ∀ v ∈ U, v ∉ Q := by
    intro v hv hvQ
    have hvK := (hUout v hv).2.2
    simp only [Q, mem_insert, mem_singleton] at hvQ
    rcases hvQ with hvQ | hvQ | hvQ <;> subst v
    · exact hvK hp
    · exact hvK hq
    · exact (hUout s hv).2.1 rfl
  have hcsA : cs ∉ A := fun h => (hUout cs hcs).2.2 (hA h)
  have hsDcard : (D.neighborFinset s).card = 3 := by
    rw [hDs, card_insert_of_notMem hcsA, hAcard]
  have hsC : C.neighborFinset s = ∅ := by
    have hh := hdegree s hsS
    change (C.neighborFinset s).card + (D.neighborFinset s).card ≤ 3 at hh
    apply card_eq_zero.mp
    omega
  have hCnone : ∀ v, ¬ C.Adj s v := by
    intro v hv
    have hh := (C.mem_neighborFinset _ _).mpr hv
    rw [hsC] at hh
    exact notMem_empty _ hh
  have hcolour : C.IsIndepSet (Q : Set V) := by
    intro a ha b hb hab
    simp only [Q, mem_coe, mem_insert, mem_singleton] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      subst a <;> subst b
    · exact C.loopless.irrefl _
    · exact hnopq
    · exact fun h => hCnone p h.symm
    · exact fun h => hnopq h.symm
    · exact C.loopless.irrefl _
    · exact fun h => hCnone q h.symm
    · exact hCnone p
    · exact hCnone q
    · exact C.loopless.irrefl _
  have hKN : ∀ v ∈ K, D.neighborFinset v ⊆ R := by
    intro v hv a ha
    have hh := hDK v hv ha
    simp only [mem_insert, mem_singleton] at hh
    rcases hh with rfl | rfl <;> simp [R]
  have hrN : D.neighborFinset r ⊆ R := by
    rw [hDr]
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · simp [R, hcr]
    · simp only [mem_insert, mem_singleton] at hv
      rcases hv with hv | hv <;> subst v
      · exact mem_union_left _ hp
      · exact mem_union_left _ hq
  have hsN : D.neighborFinset s ⊆ R := by
    rw [hDs]
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · simp [R, hcs]
    · exact mem_union_left _ (hA hv)
  have hboundary : ∀ a ∈ Q, ∀ t ∈ T, ¬ C.Adj a t ∧ ¬ D.Adj a t := by
    intro a ha t ht
    have htR := (mem_sdiff.mp ht).2
    simp only [Q, mem_insert, mem_singleton] at ha
    rcases ha with ha | ha | ha <;> subst a
    · exact ⟨fun h => htR (mem_union_left _
        (hCK p hp ((C.mem_neighborFinset _ _).mpr h))),
        fun h => htR (hKN p hp ((D.mem_neighborFinset _ _).mpr h))⟩
    · exact ⟨fun h => htR (mem_union_left _
        (hCK q hq ((C.mem_neighborFinset _ _).mpr h))),
        fun h => htR (hKN q hq ((D.mem_neighborFinset _ _).mpr h))⟩
    · exact ⟨hCnone t, fun h => htR (hsN ((D.mem_neighborFinset _ _).mpr h))⟩
  have hzero (v : V) (hN : D.neighborFinset v ⊆ R) :
      D.neighborFinset v ∩ T = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact (mem_sdiff.mp (mem_inter.mp hw).2).2 (hN (mem_inter.mp hw).1)
  have hinter : (A ∩ ({p, q} : Finset V)).card ≤ 1 := by
    have hl := card_le_card (inter_subset_left (s₁ := A) (s₂ := {p, q}))
    have hr := card_le_card (inter_subset_right (s₁ := A) (s₂ := {p, q}))
    have hPcard : ({p, q} : Finset V).card = 2 := card_pair hpq
    by_contra hh
    have hleft : A ∩ ({p, q} : Finset V) = A :=
      eq_of_subset_of_card_le inter_subset_left (by omega)
    have hright : A ∩ ({p, q} : Finset V) = {p, q} :=
      eq_of_subset_of_card_le inter_subset_right (by omega)
    exact hAP (hleft.symm.trans hright)
  have hlocal : ∀ v ∈ R, ((insert v (D.neighborFinset v)) ∩ Q).card +
      (D.neighborFinset v ∩ T).card ≤ 2 := by
    intro v hv
    rcases mem_union.mp hv with hvK | hv
    · rw [hzero v (hKN v hvK), card_empty, Nat.add_zero]
      have hsub : (insert v (D.neighborFinset v)) ∩ Q ⊆ {v, s} := by
        intro w hw
        rcases mem_insert.mp (mem_inter.mp hw).1 with hwv | hwD
        · subst w
          simp
        · have hwrs := hDK v hvK hwD
          simp only [mem_insert, mem_singleton] at hwrs
          rcases hwrs with hwrs | hwrs <;> subst w
          · exact (hrQ (mem_inter.mp hw).2).elim
          · simp
      exact (card_le_card hsub).trans card_le_two
    · rcases mem_insert.mp hv with hvr | hv
      · subst v
        rw [hzero r hrN, card_empty, Nat.add_zero]
        have hsub : (insert r (D.neighborFinset r)) ∩ Q ⊆ {p, q} := by
          intro w hw
          rw [hDr] at hw
          simp only [mem_inter, mem_insert, mem_singleton] at hw
          rcases hw.1 with hw | hw | hw
          · subst w
            exact (hrQ hw.2).elim
          · subst w
            exact (hUnQ cr hcr hw.2).elim
          · simpa only [mem_insert, mem_singleton] using hw
        exact (card_le_card hsub).trans card_le_two
      · rcases mem_insert.mp hv with hvs | hvU
        · subst v
          rw [hzero s hsN, card_empty, Nat.add_zero]
          have hsub : (insert s (D.neighborFinset s)) ∩ Q ⊆
              insert s (A ∩ ({p, q} : Finset V)) := by
            intro w hw
            have hwQ := (mem_inter.mp hw).2
            rcases mem_insert.mp (mem_inter.mp hw).1 with rfl | hw
            · simp
            · rw [hDs] at hw
              rcases mem_insert.mp hw with hwcs | hwA
              · subst w
                exact (hUnQ cs hcs hwQ).elim
              · simp only [Q, mem_insert, mem_singleton] at hwQ
                rcases hwQ with rfl | rfl | rfl
                · simp [hwA]
                · simp [hwA]
                · simp
          have hbound := card_le_card hsub
          have hinsert := card_insert_le s (A ∩ ({p, q} : Finset V))
          omega
        · have hclosedsub : (insert v (D.neighborFinset v)) ∩ Q ⊆ {s} := by
            intro w hw
            rcases mem_insert.mp (mem_inter.mp hw).1 with hwv | hwD
            · subst w
              exact (hUnQ v hvU (mem_inter.mp hw).2).elim
            · have hwQ := (mem_inter.mp hw).2
              simp only [Q, mem_insert, mem_singleton] at hwQ
              rcases hwQ with hwQ | hwQ | hwQ <;> subst w
              · have hh := hDK p hp
                  ((D.mem_neighborFinset _ _).mpr
                    ((D.mem_neighborFinset _ _).mp hwD).symm)
                simp only [mem_insert, mem_singleton] at hh
                exact (hh.elim (hUout v hvU).1 (hUout v hvU).2.1).elim
              · have hh := hDK q hq
                  ((D.mem_neighborFinset _ _).mpr
                    ((D.mem_neighborFinset _ _).mp hwD).symm)
                simp only [mem_insert, mem_singleton] at hh
                exact (hh.elim (hUout v hvU).1 (hUout v hvU).2.1).elim
              · simp
          have hqcard : ((insert v (D.neighborFinset v)) ∩ Q).card ≤ 1 := by
            simpa using card_le_card hclosedsub
          obtain ⟨y, hyR, hynQ, hye⟩ := hlost v hvU
          let N := C.neighborFinset v ∪ D.neighborFinset v
          have hNcard : N.card ≤ 3 := by
            have hh := hdegree v (hU hvU)
            change (C.neighborFinset v).card + (D.neighborFinset v).card ≤ 3 at hh
            exact (card_union_le _ _).trans hh
          have hyN : y ∈ N := by
            simpa only [N, mem_union, SimpleGraph.mem_neighborFinset] using hye
          have hyout : y ∉ D.neighborFinset v ∩ T := by
            intro hy
            exact (mem_sdiff.mp (mem_inter.mp hy).2).2 hyR
          by_cases hqzero : ((insert v (D.neighborFinset v)) ∩ Q).card = 0
          · have hsub : insert y (D.neighborFinset v ∩ T) ⊆ N := by
              intro z hz
              rcases mem_insert.mp hz with rfl | hz
              · exact hyN
              · exact mem_union_right _ (mem_inter.mp hz).1
            have hh := card_le_card hsub
            rw [card_insert_of_notMem hyout] at hh
            omega
          · have hqone : ((insert v (D.neighborFinset v)) ∩ Q).card = 1 := by omega
            obtain ⟨z, hz⟩ := card_pos.mp (by omega :
              0 < ((insert v (D.neighborFinset v)) ∩ Q).card)
            have hzs : z = s := mem_singleton.mp (hclosedsub hz)
            subst z
            have hsv : s ≠ v := (hUout v hvU).2.1.symm
            have hsD : s ∈ D.neighborFinset v := by
              rcases mem_insert.mp (mem_inter.mp hz).1 with h | h
              · exact (hsv h).elim
              · exact h
            have hsy : s ≠ y := by
              intro h
              exact hynQ (by simp [Q, ← h])
            have hsout : s ∉ insert y (D.neighborFinset v ∩ T) := by
              simp only [mem_insert, not_or]
              exact ⟨hsy, fun h => (mem_sdiff.mp (mem_inter.mp h).2).2 (by simp [R])⟩
            have hsub : insert s (insert y (D.neighborFinset v ∩ T)) ⊆ N := by
              intro z hz
              rcases mem_insert.mp hz with rfl | hz
              · exact mem_union_right _ hsD
              · rcases mem_insert.mp hz with rfl | hz
                · exact hyN
                · exact mem_union_right _ (mem_inter.mp hz).1
            have hh := card_le_card hsub
            rw [card_insert_of_notMem hsout, card_insert_of_notMem hyout] at hh
            omega
  have hvalid := extend_without_pairs C D S R Q X hR hQ hsupport hX
    hcolour hboundary hlocal hadmissible
  have hxq : Disjoint X Q := by
    apply disjoint_left.mpr
    intro v hvX hvQ
    exact (mem_sdiff.mp (hX hvX)).2 (hQ hvQ)
  have hQcard : Q.card = 3 := by
    simp [Q, hpq, show p ≠ s from fun h => hsK (h ▸ hp),
      show q ≠ s from fun h => hsK (h ▸ hq)]
  have hRcard : R.card ≤ 9 := by
    have hh := card_union_le K (insert r (insert s U))
    have hr := card_insert_le r (insert s U)
    have hs := card_insert_le s U
    dsimp only [R]
    omega
  refine ⟨X ∪ Q, union_subset (hX.trans sdiff_subset) (hQ.trans hR), hvalid, ?_⟩
  change (S \ R).card ≤ 3 * X.card at hsize
  have hsplit := card_sdiff_add_card_eq_card hR
  rw [card_union_of_disjoint hxq, hQcard]
  omega

end D5.S3.Combinatorics.SignedDoubleRoman.PackingTwoPairs

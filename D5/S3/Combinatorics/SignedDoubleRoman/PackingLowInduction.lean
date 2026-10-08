/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingLowInduction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingLowInduction
   mirror-E: none(waiver:low-degree-induction-reduction)
   anchors: []
   utility: none
   digest: A low-degree core reduces the packing induction with at most two imposing centres. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PackingLowDegree
import D5.S3.Combinatorics.SignedDoubleRoman.PackingInductionCore
import D5.S3.Combinatorics.SignedDoubleRoman.PackingPairUniqueness
import D5.S3.Combinatorics.SignedDoubleRoman.PackingTwoPairs
import D5.S3.Combinatorics.SignedDoubleRoman.MixedExtensionObstruction

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingLowInduction

open Finset MixedDefs PackingLowDegree PackingInductionCore CliqueSaturation PackingTwoPairs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With no newly created four-clique, deleting a low-degree core completes the induction. -/
theorem low_case_regular (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V) (u : V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S) (hu : u ∈ S)
    (hlow : (C.neighborFinset u ∪ D.neighborFinset u).card ≤ 2)
    (hno :
      let R := insert u (C.neighborFinset u ∪ D.neighborFinset u)
      (ReducedColour C D R {u} (S \ R)).CliqueFreeOn ((S \ R : Finset V) : Set V) 4) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  let R := insert u (C.neighborFinset u ∪ D.neighborFinset u)
  have hR : R ⊆ S := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hu
    · simp only [mem_union, SimpleGraph.mem_neighborFinset] at hx
      exact (hsupport hx).2
  obtain ⟨hcard, hc, hb, hl⟩ := low_neighbourhood_reduction C D u
    (fun x hx => hdegree x (hR hx)) hlow
  have hboundary : ∀ x ∈ ({u} : Finset V), ∀ y ∈ S \ R,
      ¬ C.Adj x y ∧ ¬ D.Adj x y := by
    intro x hx y hy
    have hxu := mem_singleton.mp hx
    subst x
    have hyR := (mem_sdiff.mp hy).2
    refine ⟨?_, ?_⟩
    · intro h
      exact hyR (hb (mem_union_left _ ((C.mem_neighborFinset _ _).mpr h)))
    · intro h
      exact hyR (hb (mem_union_right _ ((D.mem_neighborFinset _ _).mpr h)))
  have hlocal : ∀ x ∈ R,
      ((insert x (D.neighborFinset x)) ∩ ({u} : Finset V)).card ≤ 2 ∧
      (((insert x (D.neighborFinset x)) ∩ ({u} : Finset V)).card = 2 →
        D.neighborFinset x ∩ (S \ R) = ∅) ∧
      (D.neighborFinset x ∩ (S \ R)).card ≤ 2 := by
    intro x hx
    have hh := hl x hx
    have hsub : D.neighborFinset x ∩ (S \ R) ⊆ D.neighborFinset x \ R := by
      intro y hy
      exact mem_sdiff.mpr ⟨(mem_inter.mp hy).1, (mem_sdiff.mp (mem_inter.mp hy).2).2⟩
    refine ⟨hh.1, ?_, (card_le_card hsub).trans hh.2.2⟩
    intro hq
    exact eq_empty_iff_forall_notMem.mpr (fun y hy => by
      have hy' := hsub hy
      rw [hh.2.1 hq] at hy'
      exact notMem_empty _ hy')
  have hcount : R.card ≤ 3 * ({u} : Finset V).card := by
    change (insert u (C.neighborFinset u ∪ D.neighborFinset u)).card ≤ _
    simpa only [card_singleton, Nat.mul_one] using hcard
  exact reduce C D S R {u} ih hR (by simp [R]) ⟨u, by simp [R]⟩
    hcount hsupport hdegree (by simpa only [coe_singleton] using hc)
    hboundary hlocal hno


set_option maxHeartbeats 1200000 in
/-- A two-pair obstruction at a low-degree core gives a clean seven-vertex reduction. -/
theorem low_case_obstructed (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V) (u : V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hno : C.CliqueFreeOn (S : Set V) 4) (hu : u ∈ S)
    (hlow : (C.neighborFinset u ∪ D.neighborFinset u).card ≤ 2)
    (hnoA : ¬ ∃ p q r s c v : V, [p, q, r, s, c, v].Nodup ∧
      ({p, q, r, s, c, v} : Finset V) ⊆ S ∧
      C.Adj p r ∧ C.Adj p s ∧ C.Adj q r ∧ C.Adj q s ∧ C.Adj r s ∧
      (C.Adj c p ∨ D.Adj c p) ∧ (C.Adj c q ∨ D.Adj c q) ∧
      (C.Adj c v ∨ D.Adj c v))
    (K : Finset V)
    (hK : K ⊆ S \ insert u (C.neighborFinset u ∪ D.neighborFinset u))
    (hk : K.card = 4)
    (hclique : (ReducedColour C D
      (insert u (C.neighborFinset u ∪ D.neighborFinset u)) {u}
      (S \ insert u (C.neighborFinset u ∪ D.neighborFinset u))).IsClique (K : Set V)) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  let N := C.neighborFinset u ∪ D.neighborFinset u
  let R := insert u N
  let T := S \ R
  let C' := ReducedColour C D R {u} T
  have hR : R ⊆ S := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hu
    · simp only [N, mem_union, SimpleGraph.mem_neighborFinset] at hx
      exact (hsupport hx).2
  have hP (x : V) : D.neighborFinset x \ R = D.neighborFinset x ∩ T := by
    change D.neighborFinset x \ R = D.neighborFinset x ∩ (S \ R)
    ext y
    simp only [mem_sdiff, mem_inter]
    constructor
    · intro h
      exact ⟨h.1, (hsupport (Or.inr ((D.mem_neighborFinset _ _).mp h.1))).2, h.2⟩
    · intro h
      exact ⟨h.1, h.2.2⟩
  have hb : ∀ x ∈ ({u} : Finset V), ∀ y ∈ T, ¬ D.Adj x y := by
    intro x hx y hy hxy
    have hxu := mem_singleton.mp hx
    subst x
    exact (mem_sdiff.mp hy).2 (mem_insert_of_mem
      (mem_union_right _ ((D.mem_neighborFinset _ _).mpr hxy)))
  have hnot : ¬ C.IsClique (K : Set V) :=
    fun hc => hno (hK.trans sdiff_subset) ((C.isNClique_iff).2 ⟨hc, hk⟩)
  obtain ⟨p, q, hpq', hpqold⟩ := C.not_isClique_iff.mp hnot
  have hp : (p : V) ∈ K := p.property
  have hq : (q : V) ∈ K := q.property
  have hpq : (p : V) ≠ (q : V) := fun h => hpq' (Subtype.ext h)
  obtain ⟨_, r, hrR, hrQ, hrP, hrp, hrq⟩ :=
    (hclique hp hq hpq).2.2.resolve_left hpqold
  have hother : ∃ s ∈ R,
      ((insert s (D.neighborFinset s)) ∩ ({u} : Finset V)).card = 1 ∧
      (D.neighborFinset s ∩ T).card = 2 ∧
      ∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ D.Adj s a ∧ D.Adj s b ∧ s ≠ r := by
    by_contra hh
    have hcentre : ∀ c ∈ R,
        ((insert c (D.neighborFinset c)) ∩ ({u} : Finset V)).card = 1 →
        (D.neighborFinset c ∩ T).card = 2 →
        ∀ a ∈ K, ∀ b ∈ K, a ≠ b → D.Adj c a → D.Adj c b → c = r := by
      intro c hc hcQ hcP a ha b hb hab hca hcb
      by_contra hcr
      exact hh ⟨c, hc, hcQ, hcP, a, ha, b, hb, hab, hca, hcb, hcr⟩
    obtain ⟨a, b, c, d, e, f, hdist, hsub, hac, had, hbc, hbd, hcd, hea, heb, hef⟩ :=
      single_centre_obstruction C D S R {u} K r (by simp [R]) hsupport hno
        hb hcentre hK hk hclique
    exact hnoA ⟨a, b, c, d, e, f, hdist, hsub, hac, had, hbc, hbd, hcd,
      Or.inr hea, Or.inr heb, Or.inr hef⟩
  obtain ⟨s, hsR, hsQ, hsP, a, ha, b, hbK, hab, hsa, hsb, hsr⟩ := hother
  have hrs : r ≠ s := hsr.symm
  obtain ⟨hru, hruD⟩ := low_imposing_centre C D u r hrQ (by rw [hP]; exact hrP)
  obtain ⟨hsu, hsuD⟩ := low_imposing_centre C D u s hsQ (by rw [hP]; exact hsP)
  have hrN : r ∈ N := mem_union_right _ ((D.mem_neighborFinset _ _).mpr hruD.symm)
  have hsN : s ∈ N := mem_union_right _ ((D.mem_neighborFinset _ _).mpr hsuD.symm)
  have hN : N = {r, s} := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hrN
      · exact hsN
    · rw [card_pair hrs]
      exact hlow
  have hReq : R = {u, r, s} := by simp only [R, hN]
  have hKout : ∀ x ∈ K, x ≠ u ∧ x ≠ r ∧ x ≠ s := by
    intro x hx
    have h := (mem_sdiff.mp (hK hx)).2
    change x ∉ R at h
    rw [hReq] at h
    simpa only [mem_insert, mem_singleton, not_or] using h
  have hrK : r ∉ K := fun h => (hKout r h).2.1 rfl
  have hsK : s ∉ K := fun h => (hKout s h).2.2 rfl
  have huK : u ∉ K := fun h => (hKout u h).1 rfl
  have hpU : (p : V) ≠ u := (hKout p hp).1
  have hqU : (q : V) ≠ u := (hKout q hq).1
  have haU : a ≠ u := (hKout a ha).1
  have hbU : b ≠ u := (hKout b hbK).1
  have hrD : D.neighborFinset r = insert u {(p : V), (q : V)} := by
    apply (PackingSaturation.exhaust_colour D C r _ (by
      have hh := hdegree r (hR hrR)
      omega) (by simp [hpq, hpU.symm, hqU.symm]) ?_).1
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with hx | hx | hx <;> subst x
    · exact hruD
    · exact hrp
    · exact hrq
  have hsD : D.neighborFinset s = insert u {a, b} := by
    apply (PackingSaturation.exhaust_colour D C s _ (by
      have hh := hdegree s (hR hsR)
      omega) (by simp [hab, haU.symm, hbU.symm]) ?_).1
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with hx | hx | hx <;> subst x
    · exact hsuD
    · exact hsa
    · exact hsb
  have hCbound : ∀ x ∈ K, C.neighborFinset x ⊆ K := by
    intro x hx y hy
    have hh := (saturated_four_clique C D R {u} T K
      (fun x hx => hdegree x (mem_sdiff.mp hx).1) hK hk hclique x hx).2.1
    rw [hh] at hy
    exact (mem_inter.mp hy).2
  have hDbound : ∀ x ∈ K, D.neighborFinset x ⊆ {r, s} := by
    intro x hx y hy
    obtain ⟨hyR, hyQ, hyP⟩ := saturated_imposing_centres C D R {u} T K
      (fun x hx => hdegree x (mem_sdiff.mp hx).1)
      (disjoint_left.mpr (fun z hzT hzR => (mem_sdiff.mp hzT).2 hzR))
      hK hk hclique x hx y
      ((D.mem_neighborFinset _ _).mp hy)
    have hynu : y ≠ u := by
      obtain ⟨z, hz, hxz, hycard, _, _⟩ := hyP
      have hcent := low_imposing_centre C D u y hyQ (by
        rw [hP, hycard, card_pair hxz])
      exact hcent.1
    rw [hReq] at hyR
    simpa only [mem_insert, mem_singleton, hynu, false_or] using hyR
  have hAP : ({a, b} : Finset V) ≠ {(p : V), (q : V)} := by
    intro heq
    have hpairr : D.neighborFinset r ∩ T = {(p : V), (q : V)} := by
      symm
      apply eq_of_subset_of_card_le
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hrp, hK hp⟩
        · exact mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hrq, hK hq⟩
      · rw [hrP, card_pair hpq]
    have hpairs : D.neighborFinset s ∩ T = {a, b} := by
      symm
      apply eq_of_subset_of_card_le
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hsa, hK ha⟩
        · exact mem_inter.mpr ⟨(D.mem_neighborFinset _ _).mpr hsb, hK hbK⟩
      · rw [hsP, card_pair hab]
    rw [heq] at hpairs
    exact hrs (PackingPairUniqueness.saturated_pair_unique C D R {u} T K
      (fun x hx => hdegree x (mem_sdiff.mp hx).1) hK hk hclique r s p q
      hrR hsR hp hpq hpairr hpairs)
  let R2 := K ∪ insert r (insert s ({u} : Finset V))
  let T2 := S \ R2
  have hR2 : R2 ⊆ S := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact (mem_sdiff.mp (hK hx)).1
    · simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hR hrR
      · exact hR hsR
      · exact hu
  have hless : T2.card < S.card := by
    have hsplit := card_sdiff_add_card_eq_card hR2
    have hpos : 0 < R2.card := card_pos.mpr ⟨u, by simp [R2]⟩
    dsimp only [T2]
    omega
  let C2 := (C.induce (T2 : Set V)).spanningCoe
  let D2 := (D.induce (T2 : Set V)).spanningCoe
  letI : DecidableRel C2.Adj := Classical.decRel _
  letI : DecidableRel D2.Adj := Classical.decRel _
  obtain ⟨hS2, hdeg2, hno2⟩ := restriction_hypotheses C D S T2 sdiff_subset hdegree hno
  obtain ⟨X, hX, hgood, hsize⟩ := ih T2 hless C2 D2 hS2 hdeg2 hno2
  apply two_pair_reduction C D S K {u} {a, b} X p q r s u u hdegree hsupport
    (hK.trans sdiff_subset) (by simpa using hu) (hR hrR) (hR hsR) hk (by simp)
    hp hq hpq hrK hsK hrs _ (by simp) (by simp) _ (card_pair hab) hAP hrD hsD
    hCbound hDbound hpqold _ hX hsize hgood
  · apply disjoint_left.mpr
    intro x hx hx'
    have hxu := mem_singleton.mp hx
    subst x
    simpa [hru.symm, hsu.symm, huK] using hx'
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hbK
  · intro x hx
    have hxu := mem_singleton.mp hx
    subst x
    refine ⟨r, ?_, ?_, Or.inr hruD.symm⟩
    · simp
    · simp [(hKout p hp).2.1.symm, (hKout q hq).2.1.symm, hrs]


/-- The low-degree branch either lifts normally or resolves its two-centre obstruction. -/
theorem low_case (C D : SimpleGraph V)
    [DecidableRel C.Adj] [DecidableRel D.Adj] (S : Finset V) (u : V)
    (ih : ∀ T : Finset V, T.card < S.card →
      ∀ (C' D' : SimpleGraph V) [DecidableRel C'.Adj] [DecidableRel D'.Adj],
        Supported C' D' T → DegreeBound C' D' T → C'.CliqueFreeOn (T : Set V) 4 →
        ∃ X : Finset V, X ⊆ T ∧ MixedAdmissible C' D' X ∧ T.card ≤ 3 * X.card)
    (hsupport : Supported C D S) (hdegree : DegreeBound C D S)
    (hno : C.CliqueFreeOn (S : Set V) 4) (hu : u ∈ S)
    (hlow : (C.neighborFinset u ∪ D.neighborFinset u).card ≤ 2)
    (hnoA : ¬ ∃ p q r s c v : V, [p, q, r, s, c, v].Nodup ∧
      ({p, q, r, s, c, v} : Finset V) ⊆ S ∧
      C.Adj p r ∧ C.Adj p s ∧ C.Adj q r ∧ C.Adj q s ∧ C.Adj r s ∧
      (C.Adj c p ∨ D.Adj c p) ∧ (C.Adj c q ∨ D.Adj c q) ∧
      (C.Adj c v ∨ D.Adj c v)) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  let R := insert u (C.neighborFinset u ∪ D.neighborFinset u)
  by_cases hn : (ReducedColour C D R {u} (S \ R)).CliqueFreeOn ((S \ R : Finset V) : Set V) 4
  · exact low_case_regular C D S u ih hsupport hdegree hu hlow hn
  · have hn' : ∃ K : Finset V, (K : Set V) ⊆ (↑(S \ R) : Set V) ∧
        (ReducedColour C D R {u} (S \ R)).IsNClique 4 K := by
      unfold SimpleGraph.CliqueFreeOn at hn
      push_neg at hn
      exact hn
    obtain ⟨K, hK, hknc⟩ := hn'
    obtain ⟨hc, hk⟩ := (ReducedColour C D R {u} (S \ R)).isNClique_iff.mp hknc
    have hK' : K ⊆ S \ R := by
      intro x hx
      exact hK hx
    exact low_case_obstructed C D S u ih hsupport hdegree hno hu hlow hnoA K hK' hk hc

end D5.S3.Combinatorics.SignedDoubleRoman.PackingLowInduction

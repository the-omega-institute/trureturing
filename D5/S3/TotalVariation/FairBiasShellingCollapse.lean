/- GID: D5/S3/TotalVariation/FairBiasShellingCollapse
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasShellingCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A proper nonempty restriction face gives a prescribed relative collapse. -/
import D5.S3.TotalVariation.FairBiasRestriction
import D5.S3.Geometry.FiniteRelativeSimplicialCollapse

/-! The faces introduced at one facet can be deleted in a prescribed elementary collapse. -/

set_option autoImplicit false

namespace D5.S3.TotalVariation.FairBiasShellingCollapse

open D5.S3.Geometry.FiniteElementaryCollapse
open D5.S3.Geometry.FiniteRelativeSimplicialCollapse
open D5.S3.TotalVariation.FairBiasShelling
open D5.S3.TotalVariation.FairBiasRestriction

private def subfaceComplex {V : Type*} (generators : Set (Finset V)) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ ∃ B ∈ generators, s ⊆ B}
  isRelLowerSet_faces := by
    rintro s ⟨hne, B, hB, hsB⟩
    exact ⟨hne, fun t hts ht => ⟨ht, B, hB, hts.trans hsB⟩⟩

private theorem sequence_of_pairs {V : Type*} [Fintype V] [DecidableEq V]
    {L K : PreAbstractSimplicialComplex V} {v : V} (schedule : List (Finset V))
    (hLK : L ≤ K)
    (hfaces : ∀ s, (s ∈ K ∧ s ∉ L) ↔ ∃ p ∈ schedule, s = p ∨ s = insert v p)
    (hlower : ∀ p ∈ schedule, p.Nonempty ∧ v ∉ p)
    (horder : schedule.Pairwise fun p q => q.card ≤ p.card)
    (hnodup : schedule.Nodup) :
    ∃ S : Sequence K L, S.pairs.map (·.lower) = schedule ∧ ∀ P ∈ S.pairs, P.apex = v := by
  induction schedule generalizing K with
    | nil =>
      have hKL : K ≤ L := by
        intro s hs
        by_contra hn
        obtain ⟨p, hp, _⟩ := (hfaces s).mp ⟨hs, hn⟩
        exact List.not_mem_nil hp
      have heq : K = L := le_antisymm hKL hLK
      subst K
      exact ⟨.refl L, rfl, by simp [Sequence.pairs]⟩
    | cons p rest ih =>
      obtain ⟨hpne, hpv⟩ := hlower p List.mem_cons_self
      obtain ⟨hmax, hrestOrder⟩ := List.pairwise_cons.mp horder
      obtain ⟨hpRest, hrestNodup⟩ := List.nodup_cons.mp hnodup
      have hpL : p ∉ L :=
        ((hfaces p).mpr ⟨p, List.mem_cons_self, Or.inl rfl⟩).2
      have huK : insert v p ∈ K :=
        ((hfaces (insert v p)).mpr ⟨p, List.mem_cons_self, Or.inr rfl⟩).1
      have hfree : ∀ s ∈ K, p ⊂ s → s = insert v p := by
        intro s hs hps
        have hpsub := (Finset.ssubset_iff_subset_ne.mp hps).1
        have hsL : s ∉ L := fun hsL => hpL ((L.isRelLowerSet_faces hsL).2 hpsub hpne)
        obtain ⟨q, hq, hsq | hsq⟩ := (hfaces s).mp ⟨hs, hsL⟩
        · subst s
          rcases List.mem_cons.mp hq with rfl | hqRest
          · exact (Finset.ssubset_iff_subset_ne.mp hps).2 rfl |>.elim
          · exact (not_lt_of_ge (hmax q hqRest) (Finset.card_lt_card hps)).elim
        · have hpq : p ⊆ q := by
            intro x hx
            rcases Finset.mem_insert.mp (hsq ▸ hpsub hx) with rfl | hxq
            · exact (hpv hx).elim
            · exact hxq
          rcases List.mem_cons.mp hq with rfl | hqRest
          · exact hsq
          · have heq := Finset.eq_of_subset_of_card_le hpq (hmax q hqRest)
            exact (hpRest (heq ▸ hqRest)).elim
      let P : CollapsePair V := ⟨K, p, v, hpne, hpv, huK, hfree⟩
      have hLP : L ≤ P.retained := by
        intro s hs
        exact ⟨hLK hs, fun hps => hpL ((L.isRelLowerSet_faces hs).2 hps hpne)⟩
      have hrest : ∀ s, (s ∈ P.retained ∧ s ∉ L) ↔
          ∃ q ∈ rest, s = q ∨ s = insert v q := by
        intro s
        constructor
        · intro ⟨hs, hsL⟩
          obtain ⟨hsK, hp, hu⟩ := (P.mem_retained_iff s).mp hs
          obtain ⟨q, hq, he⟩ := (hfaces s).mp ⟨hsK, hsL⟩
          rcases List.mem_cons.mp hq with rfl | hqRest
          · exact (he.elim hp hu).elim
          · exact ⟨q, hqRest, he⟩
        · rintro ⟨q, hq, he⟩
          have hqd : q ∈ p :: rest := List.mem_cons_of_mem p hq
          have hqv := (hlower q hqd).2
          have hpq : q ≠ p := fun h => hpRest (h ▸ hq)
          obtain ⟨hsK, hsL⟩ := (hfaces s).mpr ⟨q, hqd, he⟩
          refine ⟨(P.mem_retained_iff s).mpr ⟨hsK, ?_, ?_⟩, hsL⟩
          · rcases he with rfl | rfl
            · exact hpq
            · intro h
              change insert v q = p at h
              exact hpv (h ▸ Finset.mem_insert_self _ _)
          · rcases he with rfl | rfl
            · exact fun h => hqv (h.symm ▸ Finset.mem_insert_self _ _)
            · intro h
              exact hpq (by
                simpa [P, CollapsePair.upper, Finset.erase_insert, hpv, hqv] using
                  congrArg (fun t : Finset V => t.erase v) h)
      obtain ⟨tail, htail, htailApex⟩ :=
        ih hLP hrest (fun q hq => hlower q (List.mem_cons_of_mem _ hq)) hrestOrder hrestNodup
      refine ⟨.step P tail, ?_, ?_⟩
      · change p :: tail.pairs.map (·.lower) = p :: rest
        rw [htail]
      · intro Q hQ
        rcases List.mem_cons.mp hQ with rfl | hQ
        · rfl
        · exact htailApex Q hQ

universe u w
variable {A : Type u} {L : Type w} [AddCommGroup A] [Module (ZMod 2) A]
  [Finite A] [Fintype L] [LinearOrder (L × Bool)]

/-- The subcomplex generated by the facets strictly before B. -/
def beforeFacet (c : L → A) (B : Finset (L × Bool)) :
    PreAbstractSimplicialComplex (L × Bool) :=
  subfaceComplex {C | C ∈ facets c ∧ lexBefore (L × Bool) C B}

/-- The subcomplex generated by B and the facets strictly before it. -/
def throughFacet (c : L → A) (B : Finset (L × Bool)) :
    PreAbstractSimplicialComplex (L × Bool) :=
  subfaceComplex (insert B {C | C ∈ facets c ∧ lexBefore (L × Bool) C B})

private theorem mem_difference_iff (c : L → A) {B s : Finset (L × Bool)}
    (hB : B ∈ facets c) (hR : (restrictionFace c B).Nonempty) :
    (s ∈ throughFacet c B ∧ s ∉ beforeFacet c B) ↔
      restrictionFace c B ⊆ s ∧ s ⊆ B := by
  constructor
  · rintro ⟨⟨hs, C, hC, hsC⟩, hnot⟩
    have hsB : s ⊆ B := by
      rcases Set.mem_insert_iff.mp hC with rfl | hc
      · exact hsC
      · exact (hnot ⟨hs, C, hc, hsC⟩).elim
    have hf : FirstAt c s B :=
      ⟨hsB, fun D hD hDB hsD => hnot ⟨hs, D, ⟨hD, hDB⟩, hsD⟩⟩
    exact ⟨(firstAt_iff_restriction_subset c hB hsB).mp hf, hsB⟩
  · rintro ⟨hRs, hsB⟩
    have hs := hR.mono hRs
    have hf := (firstAt_iff_restriction_subset c hB hsB).mpr hRs
    refine ⟨⟨hs, B, Set.mem_insert _ _, hsB⟩, ?_⟩
    rintro ⟨_, D, ⟨hD, hDB⟩, hsD⟩
    exact hf.2 D hD hDB hsD

/-- Any decreasing-cardinality enumeration of the new faces avoiding v prescribes the lower
faces of a collapse to the previous prefix. Every pair adjoins the same vertex v. -/
theorem exists_prescribed_collapse (c : L → A) {B : Finset (L × Bool)} {v : L × Bool}
    (hB : B ∈ facets c) (hR : (restrictionFace c B).Nonempty)
    (hvB : v ∈ B) (hvR : v ∉ restrictionFace c B)
    (schedule : List (Finset (L × Bool)))
    (hcoverage : ∀ s, s ∈ schedule ↔ restrictionFace c B ⊆ s ∧ s ⊆ B ∧ v ∉ s)
    (horder : schedule.Pairwise fun p q => q.card ≤ p.card) (hnodup : schedule.Nodup) :
    ∃ S : Sequence (throughFacet c B) (beforeFacet c B),
      S.pairs.map (·.lower) = schedule ∧ ∀ P ∈ S.pairs, P.apex = v := by
  let _ : DecidableEq (L × Bool) := LinearOrder.toDecidableEq
  have hle : beforeFacet c B ≤ throughFacet c B := by
    rintro s ⟨hs, D, hD, hsD⟩
    exact ⟨hs, D, Set.mem_insert_of_mem _ hD, hsD⟩
  apply sequence_of_pairs (v := v) schedule hle ?_ ?_ horder hnodup
  · intro s
    rw [mem_difference_iff c hB hR]
    constructor
    · rintro ⟨hRs, hsB⟩
      by_cases hsv : v ∈ s
      · refine ⟨s.erase v, (hcoverage _).mpr ⟨?_, ?_, Finset.notMem_erase _ _⟩,
          Or.inr (Finset.insert_erase hsv).symm⟩
        · exact Finset.subset_erase.mpr ⟨hRs, hvR⟩
        · exact (Finset.erase_subset _ _).trans hsB
      · exact ⟨s, (hcoverage _).mpr ⟨hRs, hsB, hsv⟩, Or.inl rfl⟩
    · rintro ⟨p, hp, rfl | rfl⟩
      · exact ⟨((hcoverage _).mp hp).1, ((hcoverage _).mp hp).2.1⟩
      · obtain ⟨hRp, hpB, _⟩ := (hcoverage _).mp hp
        exact ⟨hRp.trans (Finset.subset_insert _ _), Finset.insert_subset hvB hpB⟩
  · intro p hp
    obtain ⟨hRp, _, hpv⟩ := (hcoverage _).mp hp
    exact ⟨hR.mono hRp, hpv⟩

end D5.S3.TotalVariation.FairBiasShellingCollapse

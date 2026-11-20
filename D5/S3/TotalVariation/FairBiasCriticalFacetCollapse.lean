/- GID: D5/S3/TotalVariation/FairBiasCriticalFacetCollapse
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasCriticalFacetCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Excluding the full-restriction facets leaves a complex collapsing to the first. -/
import D5.S3.TotalVariation.FairBiasShellingCollapse
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

/-! Relative collapse after omitting the full-restriction facets of the signed complex. -/

set_option autoImplicit false

namespace D5.S3.TotalVariation.FairBiasCriticalFacetCollapse

open D5.S3.Geometry.FiniteElementaryCollapse
open D5.S3.Geometry.FiniteRelativeSimplicialCollapse
open D5.S3.TotalVariation.FairBiasLink
open D5.S3.TotalVariation.FairBiasShelling
open D5.S3.TotalVariation.FairBiasRestriction
open D5.S3.TotalVariation.FairBiasShellingCollapse

private def omitSupersets {V : Type*} (excluded : Set (Finset V))
    (K : PreAbstractSimplicialComplex V) : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ K ∧ ∀ q ∈ excluded, ¬ q ⊆ s}
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨hsK, hsExcluded⟩ : s ∈ K ∧ ∀ q ∈ excluded, ¬ q ⊆ s := hs
    obtain ⟨hsne, hdown⟩ := K.isRelLowerSet_faces hsK
    refine ⟨hsne, ?_⟩
    intro t hts ht
    exact ⟨hdown hts ht, fun q hq hqt => hsExcluded q hq (hqt.trans hts)⟩

private theorem sequence_omitSupersets {V : Type*} [Fintype V] [DecidableEq V]
    {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)
    (excluded : Set (Finset V)) (h : ∀ P ∈ S.pairs, ∀ q ∈ excluded, ¬ q ⊆ P.upper) :
    Nonempty (Sequence (omitSupersets excluded K) (omitSupersets excluded L)) := by
  induction S with
  | refl K => exact ⟨.refl _⟩
  | step P tail ih =>
      have hupper : ∀ q ∈ excluded, ¬ q ⊆ P.upper := h P List.mem_cons_self
      let trimmed : CollapsePair V :=
        { ambient := omitSupersets excluded P.ambient
          lower := P.lower
          apex := P.apex
          lower_nonempty := P.lower_nonempty
          apex_notMem := P.apex_notMem
          upper_mem := ⟨P.upper_mem, hupper⟩
          free := fun s hs hls => P.free s hs.1 hls }
      have hcommute : omitSupersets excluded P.retained = trimmed.retained := by
        apply SetLike.ext
        intro s
        change ((s ∈ P.ambient ∧ ¬ P.lower ⊆ s) ∧ ∀ q ∈ excluded, ¬ q ⊆ s) ↔
          ((s ∈ P.ambient ∧ ∀ q ∈ excluded, ¬ q ⊆ s) ∧ ¬ P.lower ⊆ s)
        exact ⟨fun ⟨⟨hs, hp⟩, hq⟩ => ⟨⟨hs, hq⟩, hp⟩,
          fun ⟨⟨hs, hq⟩, hp⟩ => ⟨⟨hs, hp⟩, hq⟩⟩
      obtain ⟨trimmedTail⟩ := ih (fun Q hQ => h Q (List.mem_cons_of_mem P hQ))
      exact ⟨.step trimmed (trimmedTail.cast hcommute rfl)⟩

universe u w
variable {A : Type u} {E : Type w} [AddCommGroup A] [Module (ZMod 2) A]
  [Finite A] [Fintype E] [LinearOrder (E × Bool)]

/-- The maximal faces whose entire boundary lies in earlier facets. -/
def fullRestrictionFacets (c : E → A) : Set (Finset (E × Bool)) :=
  {B | B ∈ facets c ∧ restrictionFace c B = B}

/-- The complex with exactly the full-restriction facets removed. -/
def retainedComplex (c : E → A) : PreAbstractSimplicialComplex (E × Bool) where
  faces := {s | s ∈ signedComplex c ∧ s ∉ fullRestrictionFacets c}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsc⟩
    refine ⟨((signedComplex c).isRelLowerSet_faces hs).1, ?_⟩
    intro t hts ht
    refine ⟨((signedComplex c).isRelLowerSet_faces hs).2 hts ht, ?_⟩
    intro htc
    have he := (mem_facets.mp htc.1).2 s hs hts
    exact hsc (he.symm ▸ htc)

/-- The simplex consisting of the nonempty subfaces of a given finite set. -/
def simplexOn {V : Type*} (B : Finset V) : PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ s ⊆ B}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht => ⟨ht, hts.trans hs.2⟩⟩

theorem subface_of_facet (c : E → A) {B s : Finset (E × Bool)}
    (hB : B ∈ facets c) (hs : s.Nonempty) (hsB : s ⊆ B) : s ∈ signedComplex c :=
  ((signedComplex c).isRelLowerSet_faces (mem_facets.mp hB).1).2 hsB hs

private theorem through_le_signed (c : E → A) {B : Finset (E × Bool)}
    (hB : B ∈ facets c) : throughFacet c B ≤ signedComplex c := by
  rintro s ⟨hs, C, hC, hsC⟩
  rcases Set.mem_insert_iff.mp hC with rfl | hC
  · exact subface_of_facet c hB hs hsC
  · exact subface_of_facet c hC.1 hs hsC


private theorem collapse_pruned_step (c : E → A) {B : Finset (E × Bool)}
    (hB : B ∈ facets c) (hPrev : ∃ T ∈ facets c, lexBefore (E × Bool) T B) :
    Nonempty (Sequence (omitSupersets (fullRestrictionFacets c) (throughFacet c B))
      (omitSupersets (fullRestrictionFacets c) (beforeFacet c B))) := by
  classical
  have hRsub : restrictionFace c B ⊆ B := Finset.filter_subset _ _
  let _ : DecidableEq (E × Bool) := LinearOrder.toDecidableEq
  by_cases hFull : restrictionFace c B = B
  · have heq : omitSupersets (fullRestrictionFacets c) (throughFacet c B) =
        omitSupersets (fullRestrictionFacets c) (beforeFacet c B) := by
      apply SetLike.ext
      intro s
      constructor
      · rintro ⟨hs, hexcluded⟩
        by_cases hEarlier : s ∈ beforeFacet c B
        · exact ⟨hEarlier, hexcluded⟩
        · obtain ⟨hsne, C, hC, hsC⟩ := hs
          have hsB : s ⊆ B := by
            rcases Set.mem_insert_iff.mp hC with rfl | hC
            · exact hsC
            · exact (hEarlier ⟨hsne, C, hC, hsC⟩).elim
          have hFirst : FirstAt c s B :=
            ⟨hsB, fun T hT hTB hsT => hEarlier ⟨hsne, T, ⟨hT, hTB⟩, hsT⟩⟩
          have hBs : B ⊆ s := by
            rw [← hFull]
            exact (firstAt_iff_restriction_subset c hB hsB).mp hFirst
          exact (hexcluded B ⟨hB, hFull⟩ hBs).elim
      · rintro ⟨⟨hsne, C, hC, hsC⟩, hexcluded⟩
        exact ⟨⟨hsne, C, Set.mem_insert_of_mem _ hC, hsC⟩, hexcluded⟩
    exact ⟨(.refl _ : Sequence _ _).cast heq.symm rfl⟩
  · have hR : (restrictionFace c B).Nonempty := by
      by_contra hEmpty
      have hsub : (∅ : Finset (E × Bool)) ⊆ B := Finset.empty_subset _
      have hFirst := (firstAt_iff_restriction_subset c hB hsub).mpr
        (by rw [Finset.not_nonempty_iff_eq_empty.mp hEmpty])
      obtain ⟨T, hT, hTB⟩ := hPrev
      exact hFirst.2 T hT hTB (Finset.empty_subset _)
    have hNotSub : ¬ B ⊆ restrictionFace c B :=
      fun hs => hFull (Finset.Subset.antisymm hRsub hs)
    obtain ⟨v, hvB, hvR⟩ := Finset.not_subset.mp hNotSub
    let lowerFaces : Finset (Finset (E × Bool)) :=
      Finset.univ.filter fun s => restrictionFace c B ⊆ s ∧ s ⊆ B ∧ v ∉ s
    let schedule := lowerFaces.toList.mergeSort fun p q => decide (q.card ≤ p.card)
    have hCoverage (s : Finset (E × Bool)) :
        s ∈ schedule ↔ restrictionFace c B ⊆ s ∧ s ⊆ B ∧ v ∉ s := by
      simp [schedule, lowerFaces]
    have hOrder : schedule.Pairwise (fun p q => q.card ≤ p.card) := by
      simpa [schedule] using
        (List.pairwise_mergeSort (le := fun p q : Finset (E × Bool) => decide (q.card ≤ p.card))
          (fun a b d hab hbd => by
            simpa using (le_trans (of_decide_eq_true hbd) (of_decide_eq_true hab) :
              d.card ≤ a.card))
          (fun a b => by simpa using le_total b.card a.card) lowerFaces.toList)
    have hNodup : schedule.Nodup := (List.nodup_mergeSort).mpr lowerFaces.nodup_toList
    obtain ⟨S, hSchedule, hApex⟩ :=
      exists_prescribed_collapse c hB hR hvB hvR schedule hCoverage hOrder hNodup
    apply sequence_omitSupersets S (fullRestrictionFacets c)
    intro P hP Q hQ hQU
    have hLower : P.lower ∈ schedule := by
      rw [← hSchedule]
      exact List.mem_map.mpr ⟨P, hP, rfl⟩
    have hUpper : P.upper ⊆ B := by
      change insert P.apex P.lower ⊆ B
      rw [hApex P hP]
      exact Finset.insert_subset hvB ((hCoverage P.lower).mp hLower).2.1
    have hBQ : B = Q := (mem_facets.mp hQ.1).2 B (mem_facets.mp hB).1
      (hQU.trans hUpper)
    exact hFull (hBQ ▸ hQ.2)

private noncomputable def earlier (c : E → A) (B : Finset (E × Bool)) : Finset (Finset (E × Bool)) := by
  classical
  exact (facets c).filter (fun C => lexBefore (E × Bool) C B)

private theorem mem_earlier {c : E → A} {B C : Finset (E × Bool)} :
    C ∈ earlier c B ↔ C ∈ facets c ∧ lexBefore (E × Bool) C B := by
  classical
  simp [earlier]

private theorem before_eq_through_predecessor (c : E → A) {B T : Finset (E × Bool)}
    (hT : T ∈ earlier c B)
    (hTmost : ∀ C ∈ earlier c B, ¬ lexBefore (E × Bool) T C) :
    beforeFacet c B = throughFacet c T := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hs, C, hC, hsC⟩
    have hCe := mem_earlier.mpr hC
    rcases lt_trichotomy (toColex (α := Finset (E × Bool)ᵒᵈ) C)
        (toColex (α := Finset (E × Bool)ᵒᵈ) T) with h | h | h
    · exact (hTmost C hCe h).elim
    · exact ⟨hs, C, Set.mem_insert_iff.mpr (Or.inl (toColex.injective h)), hsC⟩
    · exact ⟨hs, C, Set.mem_insert_of_mem _ ⟨hC.1, h⟩, hsC⟩
  · rintro ⟨hs, C, hC, hsC⟩
    have hT' := mem_earlier.mp hT
    rcases Set.mem_insert_iff.mp hC with rfl | hC
    · exact ⟨hs, C, hT', hsC⟩
    · have hCT : toColex (α := Finset (E × Bool)ᵒᵈ) T <
          toColex (α := Finset (E × Bool)ᵒᵈ) C := hC.2
      exact ⟨hs, C, ⟨hC.1, lt_trans hT'.2 hCT⟩, hsC⟩

private theorem earlier_card_lt (c : E → A) {B T : Finset (E × Bool)}
    (hT : T ∈ earlier c B) : (earlier c T).card < (earlier c B).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro C hC
    have hCT := (mem_earlier.mp hC).2
    exact mem_earlier.mpr ⟨(mem_earlier.mp hC).1, lt_trans (mem_earlier.mp hT).2 hCT⟩
  · intro he
    have hTT : lexBefore (E × Bool) T T := (mem_earlier.mp (he.symm ▸ hT)).2
    exact lt_irrefl _ hTT

private theorem first_prefix_eq_simplex (c : E → A) {B : Finset (E × Bool)}
    (hB : B ∈ facets c) (hfirst : ∀ C ∈ facets c, ¬ lexBefore (E × Bool) C B) :
    omitSupersets (fullRestrictionFacets c) (throughFacet c B) = simplexOn B := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨⟨hs, C, hC, hsC⟩, _⟩
    rcases Set.mem_insert_iff.mp hC with rfl | hC
    · exact ⟨hs, hsC⟩
    · exact (hfirst C hC.1 hC.2).elim
  · rintro ⟨hs, hsB⟩
    refine ⟨⟨hs, B, Set.mem_insert _ _, hsB⟩, ?_⟩
    intro C hC hCs
    have he := (mem_facets.mp hC.1).2 B (mem_facets.mp hB).1 (hCs.trans hsB)
    subst C
    have hr : restrictionFace c B = ∅ :=
      Finset.subset_empty.mp ((firstAt_iff_restriction_subset c hB
        (Finset.empty_subset B)).mp ⟨Finset.empty_subset _, fun C hC hCB =>
          (hfirst C hC hCB).elim⟩)
    have hne := (signedComplex c).isRelLowerSet_faces (mem_facets.mp hB).1 |>.1
    exact hne.ne_empty (hC.2.symm.trans hr)

private theorem last_prefix_eq_retained (c : E → A) {B : Finset (E × Bool)}
    (hB : B ∈ facets c) (hlast : ∀ C ∈ facets c, ¬ lexBefore (E × Bool) B C) :
    omitSupersets (fullRestrictionFacets c) (throughFacet c B) = retainedComplex c := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨hs, hsC⟩
    exact ⟨through_le_signed c hB hs, fun h => hsC s h (Finset.Subset.refl _)⟩
  · rintro ⟨hs, hsNot⟩
    obtain ⟨C, hC, hsC⟩ := exists_facet_superset c hs
    have hCv : C ∈ insert B {T | T ∈ facets c ∧ lexBefore (E × Bool) T B} := by
      rcases lt_trichotomy (toColex (α := Finset (E × Bool)ᵒᵈ) C)
          (toColex (α := Finset (E × Bool)ᵒᵈ) B) with h | h | h
      · exact (hlast C hC h).elim
      · exact Set.mem_insert_iff.mpr (Or.inl (toColex.injective h))
      · exact Set.mem_insert_of_mem _ ⟨hC, h⟩
    refine ⟨⟨((signedComplex c).isRelLowerSet_faces hs).1, C, hCv, hsC⟩, ?_⟩
    intro Q hQ hQs
    have he := (mem_facets.mp hQ.1).2 s hs hQs
    exact hsNot (he.symm ▸ hQ)

/-- Removing precisely the full-restriction facets leaves a complex that collapses to the
single simplex generated by the first facet in the given order. -/
theorem exists_collapse_to_first_facet (c : E → A) (h : (facets c).Nonempty) :
    ∃ B ∈ facets c, (∀ C ∈ facets c, ¬ lexBefore (E × Bool) C B) ∧
      Nonempty (Sequence (retainedComplex c) (simplexOn B)) := by
  classical
  let _ : DecidableEq (E × Bool) := LinearOrder.toDecidableEq
  have fromPrefix (n : ℕ) (B : Finset (E × Bool)) (hB : B ∈ facets c)
      (hn : (earlier c B).card = n) :
      ∃ F ∈ facets c, (∀ C ∈ facets c, ¬ lexBefore (E × Bool) C F) ∧
        Nonempty (Sequence (omitSupersets (fullRestrictionFacets c) (throughFacet c B))
          (simplexOn F)) := by
    induction n using Nat.strong_induction_on generalizing B with
    | h n ih =>
      by_cases he : (earlier c B).Nonempty
      · obtain ⟨T, hT, hmax⟩ := (earlier c B).exists_max_image
          (fun C => OrderDual.toDual (toColex (α := Finset (E × Bool)ᵒᵈ) C)) he
        have hTmost : ∀ C ∈ earlier c B, ¬ lexBefore (E × Bool) T C :=
          fun C hC => not_lt_of_ge (hmax C hC)
        have hbefore := before_eq_through_predecessor c hT hTmost
        have hsmall := earlier_card_lt c hT
        rw [hn] at hsmall
        obtain ⟨F, hF, hfirst, ⟨tail⟩⟩ := ih _ hsmall T (mem_earlier.mp hT).1 rfl
        obtain ⟨step⟩ := collapse_pruned_step c hB ⟨T, (mem_earlier.mp hT).1,
          (mem_earlier.mp hT).2⟩
        have htarget := congrArg (omitSupersets (fullRestrictionFacets c)) hbefore
        exact ⟨F, hF, hfirst, ⟨(step.cast rfl htarget).append tail⟩⟩
      · have hfirst : ∀ C ∈ facets c, ¬ lexBefore (E × Bool) C B :=
          fun C hC hCB => he ⟨C, mem_earlier.mpr ⟨hC, hCB⟩⟩
        exact ⟨B, hB, hfirst, ⟨(Sequence.refl (simplexOn B)).cast
          (first_prefix_eq_simplex c hB hfirst).symm rfl⟩⟩
  obtain ⟨B, hB, hmax⟩ := (facets c).exists_max_image
    (fun C => OrderDual.toDual (toColex (α := Finset (E × Bool)ᵒᵈ) C)) h
  have hlast : ∀ C ∈ facets c, ¬ lexBefore (E × Bool) B C :=
    fun C hC => not_lt_of_ge (hmax C hC)
  obtain ⟨F, hF, hfirst, ⟨S⟩⟩ := fromPrefix _ B hB rfl
  exact ⟨F, hF, hfirst, ⟨S.cast (last_prefix_eq_retained c hB hlast) rfl⟩⟩

end D5.S3.TotalVariation.FairBiasCriticalFacetCollapse

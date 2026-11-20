/- GID: D5/S3/TotalVariation/FairBiasShelling
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FairBiasShelling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Maximal signed fair-bias faces have uniform size and obey lexicographic shelling. -/

import D5.S3.TotalVariation.FairBiasFaceCount
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Combinatorics.Matroid.Closure

/-! The nonempty faces of the fair-bias link are the independent sets of a signed matroid. -/

set_option autoImplicit false

open Set
open scoped Matroid

namespace D5.S3.TotalVariation.FairBiasShelling

open D5.S3.TotalVariation.FairBiasLink
open D5.S3.TotalVariation.FairBiasFaceCount

universe u v

variable {A : Type u} {L : Type v} [AddCommGroup A] [Module (ZMod 2) A] [Finite A] [Fintype L]

private theorem span_rank_of_indep (c : L → A) (S : Set L)
    (hS : LinearIndepOn (ZMod 2) c S) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (c '' S)) = S.ncard := by
  classical
  let _ : Fintype S := Fintype.ofFinite _
  rw [← Set.range_domRestrict, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact finrank_span_eq_card hS

private noncomputable def columnMatroid (c : L → A) : Matroid L :=
  (IndepMatroid.ofFinite Set.finite_univ (LinearIndepOn (ZMod 2) c)
    (linearIndepOn_empty _ _) (fun _ _ h hs => h.mono hs) (by
      intro I J hI hJ hcard
      by_contra hn
      have hsub : Submodule.span (ZMod 2) (c '' J) ≤ Submodule.span (ZMod 2) (c '' I) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i, hi, rfl⟩
        by_cases h : i ∈ I
        · exact Submodule.subset_span ⟨i, h, rfl⟩
        · by_contra hnmem
          exact hn ⟨i, hi, h, (linearIndepOn_insert h).mpr ⟨hI, hnmem⟩⟩
      let _ : Module.Finite (ZMod 2) (Submodule.span (ZMod 2) (c '' I)) := Module.Finite.of_finite
      have hle := Submodule.finrank_mono hsub
      rw [span_rank_of_indep c J hJ, span_rank_of_indep c I hI] at hle
      exact (not_le_of_gt hcard) hle)
    (fun _ _ => Set.subset_univ _)).matroid

private theorem column_isBase_iff (c : L → A) (B : Set L) :
    (columnMatroid c).IsBase B ↔
      LinearIndepOn (ZMod 2) c B ∧
        Submodule.span (ZMod 2) (c '' B) = Submodule.span (ZMod 2) (Set.range c) := by
  rw [Matroid.isBase_iff_maximal_indep, maximal_subset_iff]
  change (LinearIndepOn (ZMod 2) c B ∧
    ∀ ⦃T : Set L⦄, LinearIndepOn (ZMod 2) c T → B ⊆ T → B = T) ↔ _
  constructor
  · rintro ⟨hB, hmax⟩
    refine ⟨hB, le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_⟩
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ B
    · exact Submodule.subset_span ⟨i, hi, rfl⟩
    · by_contra hn
      have he := hmax ((linearIndepOn_insert hi).mpr ⟨hB, hn⟩) (Set.subset_insert i B)
      exact hi (he ▸ Set.mem_insert i B)
  · rintro ⟨hB, hspan⟩
    refine ⟨hB, fun T hT hBT => hBT.antisymm ?_⟩
    intro i hi
    by_contra hn
    have hI := hT.mono (Set.insert_subset hi hBT)
    have hnot := ((linearIndepOn_insert hn).mp hI).2
    exact hnot (hspan.symm ▸ Submodule.subset_span (Set.mem_range_self i))

private theorem column_spanning_iff (c : L → A) (S : Set L) :
    (columnMatroid c).Spanning S ↔
      Submodule.span (ZMod 2) (c '' S) = Submodule.span (ZMod 2) (Set.range c) := by
  rw [Matroid.spanning_iff_exists_isBase_subset (by exact Set.subset_univ _)]
  constructor
  · rintro ⟨B, hB, hBS⟩
    apply le_antisymm (Submodule.span_mono (Set.image_subset_range _ _))
    rw [← ((column_isBase_iff c B).mp hB).2]
    exact Submodule.span_mono (Set.image_mono hBS)
  · intro hS
    obtain ⟨B, hBS, _, hspan, hB⟩ :=
      exists_linearIndepOn_extension (linearIndepOn_empty (ZMod 2) c) (Set.empty_subset S)
    refine ⟨B, (column_isBase_iff c B).mpr ⟨hB, ?_⟩, hBS⟩
    rw [← hS]
    exact le_antisymm (Submodule.span_mono (Set.image_mono hBS)) (Submodule.span_le.mpr hspan)

/-- The dual column matroid pulled back to the two signs of each label. -/
noncomputable def signedMatroid (c : L → A) : Matroid (L × Bool) :=
  ((columnMatroid c)✶).comap Prod.fst

private theorem face_iff_indep (c : L → A) (S : Finset (L × Bool)) :
    S ∈ signedComplex c ↔ S.Nonempty ∧ (signedMatroid c).Indep (S : Set (L × Bool)) := by
  classical
  change (S.Nonempty ∧ (∀ i, (i, true) ∈ S → (i, false) ∉ S) ∧
    AddSubgroup.closure (c '' {i | ∀ b : Bool, (i, b) ∉ S}) = AddSubgroup.closure (Set.range c)) ↔ _
  have hcomplement : {i | ∀ b : Bool, (i, b) ∉ S} =
      (Prod.fst '' (S : Set (L × Bool)))ᶜ := by
    ext i
    constructor
    · rintro h ⟨⟨j, b⟩, hj, rfl⟩
      exact h b hj
    · intro h b hb
      exact h ⟨(i, b), hb, rfl⟩
  have hsign : (∀ i, (i, true) ∈ S → (i, false) ∉ S) ↔
      Set.InjOn Prod.fst (S : Set (L × Bool)) := by
    refine ⟨fst_injOn, ?_⟩
    intro h i ht hf
    have he := h ht hf (rfl : (i, true).1 = (i, false).1)
    cases he
  rw [signedMatroid, Matroid.comap_indep_iff, hsign, hcomplement, ← Matroid.Coindep,
    Matroid.coindep_iff_compl_spanning (by exact Set.subset_univ _)]
  rw [show (columnMatroid c).E = Set.univ from rfl, ← Set.compl_eq_univ_sdiff,
    column_spanning_iff, ← span_as_closure, ← span_as_closure]
  rw [Submodule.toAddSubgroup_injective.eq_iff]
  exact and_congr_right (fun _ => and_comm)

/-- A maximal nonempty face in the signed simplicial complex. -/
def IsFacet (c : L → A) (S : Finset (L × Bool)) : Prop :=
  S ∈ signedComplex c ∧ ∀ T ∈ signedComplex c, S ⊆ T → T = S

private theorem facet_iff_base (c : L → A) (S : Finset (L × Bool)) :
    IsFacet c S ↔ S.Nonempty ∧ (signedMatroid c).IsBase (S : Set (L × Bool)) := by
  classical
  constructor
  · rintro ⟨hS, hmax⟩
    obtain ⟨hne, hI⟩ := (face_iff_indep c S).mp hS
    refine ⟨hne, hI.isBase_of_maximal ?_⟩
    intro T hT hST
    let U := (Set.toFinite T).toFinset
    have hU : (U : Set (L × Bool)) = T := Set.Finite.coe_toFinset _
    have hSU : S ⊆ U := Finset.coe_subset.mp (hU.symm ▸ hST)
    have he := hmax U ((face_iff_indep c U).mpr ⟨hne.mono hSU, hU.symm ▸ hT⟩) hSU
    exact (congrArg (fun F : Finset (L × Bool) => (F : Set (L × Bool))) he).symm.trans hU
  · rintro ⟨hne, hS⟩
    refine ⟨(face_iff_indep c S).mpr ⟨hne, hS.indep⟩, ?_⟩
    intro T hT hST
    exact Finset.coe_injective
      (hS.eq_of_subset_indep ((face_iff_indep c T).mp hT).2 (Finset.coe_subset.mpr hST)).symm

/-- Each maximal nonempty face has as many labels as the nullity of the column family. -/
theorem facet_card_eq_nullity (c : L → A) (S : Finset (L × Bool)) (hS : IsFacet c S) :
    S.card = Fintype.card L - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range c)) := by
  classical
  let B := Prod.fst '' (S : Set (L × Bool))
  have hbase := ((facet_iff_base c S).mp hS).2
  have hpre : Prod.fst '' (Prod.fst ⁻¹' ((columnMatroid c)✶).E : Set (L × Bool)) =
      ((columnMatroid c)✶).E := by
    exact Set.image_preimage_eq _ (fun i => ⟨(i, false), rfl⟩)
  have hproj := (Matroid.comap_isBase_iff.mp hbase)
  rw [hpre, Matroid.isBasis_ground_iff] at hproj
  have hB : (columnMatroid c).IsBase Bᶜ := by
    have h := hproj.1.compl_isBase_of_dual
    change (columnMatroid c).IsBase (Set.univ \ B) at h
    simpa only [Set.compl_eq_univ_sdiff] using h
  obtain ⟨hI, hspan⟩ := (column_isBase_iff c Bᶜ).mp hB
  have hr := span_rank_of_indep c Bᶜ hI
  rw [hspan, Set.ncard_compl] at hr
  have hcard : B.ncard = S.card := hproj.2.1.ncard_image.trans (Set.ncard_coe_finset S)
  rw [hcard, Nat.card_eq_fintype_card] at hr
  have hle : S.card ≤ Fintype.card L := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, hcard] using
      (Set.ncard_le_ncard (Set.subset_univ B))
  omega

/-- Lexicographic precedence of equal-size faces, using the first differing signed vertex. -/
def lexBefore (α : Type*) [LinearOrder α] (S T : Finset α) : Prop :=
  toColex (α := Finset αᵒᵈ) T < toColex (α := Finset αᵒᵈ) S

private theorem lexBefore_iff {α : Type*} [LinearOrder α] {S T : Finset α} :
    lexBefore α S T ↔ ∃ x ∈ S, x ∉ T ∧ ∀ y ∈ T, y ∉ S → x < y :=
  Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt (α := αᵒᵈ)

/-- Lexicographic order on the signed labels satisfies the facet shelling criterion. -/
theorem lexicographic_facet_shelling (c : L → A) [LinearOrder (L × Bool)]
    (S T : Finset (L × Bool)) (hS : IsFacet c S) (hT : IsFacet c T)
    (hST : lexBefore (L × Bool) S T) :
    ∃ U : Finset (L × Bool), IsFacet c U ∧ lexBefore (L × Bool) U T ∧
      (↑S : Set (L × Bool)) ∩ ↑T ⊆ ↑U ∧ ∃ y, (↑T : Set (L × Bool)) \ ↑U = {y} := by
  classical
  obtain ⟨x, hxS, hxT, hfirst⟩ := lexBefore_iff.mp hST
  let M := signedMatroid c
  have hBS := ((facet_iff_base c S).mp hS).2
  have hBT := ((facet_iff_base c T).mp hT).2
  let I := insert x ((S : Set (L × Bool)) ∩ T)
  have hI : M.Indep I := hBS.indep.subset (Set.insert_subset hxS Set.inter_subset_left)
  obtain ⟨V, hV, hIV, hVI⟩ := hI.exists_isBase_subset_union_isBase hBT
  have hxV : x ∈ V := hIV (Set.mem_insert _ _)
  have hVT : V ⊆ insert x (T : Set (L × Bool)) := by
    intro z hz
    rcases hVI hz with hz | hz
    · rcases hz with rfl | hh
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ hh.2
    · exact Set.mem_insert_of_mem _ hz
  have hn : ¬ (T : Set (L × Bool)) ⊆ V := by
    intro hs
    apply hxT
    change x ∈ (T : Set (L × Bool))
    rwa [hBT.eq_of_subset_isBase hV hs]
  obtain ⟨y, hyT, hyV⟩ := Set.not_subset.mp hn
  have hyS : y ∉ S := fun hy => hyV (hIV (Set.mem_insert_of_mem _ ⟨hy, hyT⟩))
  have hVeq : V = insert x ((T : Set (L × Bool)) \ {y}) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro z hz
      rcases hVT hz with rfl | ht
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨ht, fun hzy => hyV (hzy ▸ hz)⟩
    · rw [Set.ncard_insert_of_notMem (fun hz => hxT hz.1) (Set.toFinite _),
        Set.ncard_sdiff_singleton_add_one hyT (Set.toFinite _), hBT.ncard_eq_ncard_of_isBase hV]
  let U := (Set.toFinite V).toFinset
  have hU : (U : Set (L × Bool)) = V := Set.Finite.coe_toFinset _
  have hxU : x ∈ U := by change x ∈ (U : Set (L × Bool)); rwa [hU]
  refine ⟨U, (facet_iff_base c U).mpr ⟨⟨x, hxU⟩, hU.symm ▸ hV⟩, ?_, ?_, y, ?_⟩
  · refine lexBefore_iff.mpr ⟨x, hxU, hxT, ?_⟩
    intro z hzT hzU
    have hzV : z ∉ V := by
      rw [← hU]
      exact hzU
    have hzy : z = y := by
      by_contra hne
      exact hzV (hVeq.symm ▸ Set.mem_insert_of_mem x ⟨hzT, hne⟩)
    exact hzy.symm ▸ hfirst y hyT hyS
  · rw [hU]
    exact fun z hz => hIV (Set.mem_insert_of_mem x hz)
  · rw [hU, hVeq]
    ext z
    constructor
    · intro hz
      by_contra hnz
      exact hz.2 (Set.mem_insert_of_mem _ ⟨hz.1, hnz⟩)
    · rintro rfl
      exact ⟨hyT, fun hz => hyV (hVeq.symm ▸ hz)⟩

end D5.S3.TotalVariation.FairBiasShelling

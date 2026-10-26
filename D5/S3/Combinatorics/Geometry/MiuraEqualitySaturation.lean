/- GID: D5/S3/Combinatorics/Geometry/MiuraEqualitySaturation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraEqualitySaturation
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Saturated actual slab charges uniquely realize matching rectangles. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraSlabRunBound
import all D5.S3.Combinatorics.Geometry.MiuraSlabBudget
public import Mathlib.Data.Fintype.EquivFin

/-! Equality saturates the actual matching-cell injection. -/

@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraEqualitySaturation
open MiuraHeightEnvelope MiuraSlabExtrema MiuraSlabNeutral MiuraSlabIncidence
open MiuraSlabBudget MiuraSlabRunBound MiuraSlabCover
variable {m n : ℕ}

private abbrev Matching (h : Cell m n → ℤ) :=
  ↥((minRowSlabs h) ×ˢ (minColSlabs h)) ⊕
  ↥((maxRowSlabs h) ×ˢ (maxColSlabs h))

private def Matches (h : Cell m n → ℤ) (p : Matching h) (v : Cell m n) : Prop :=
  match p with
  | .inl p => p.val.1.Contains v.1 ∧ p.val.2.Contains v.2 ∧ IsStrictLocalMin h v
  | .inr p => p.val.1.Contains v.1 ∧ p.val.2.Contains v.2 ∧ IsStrictLocalMax h v

private theorem matching_equiv {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n)
    (heq : (extrema h).card = (neutralRowSlabs h).card + (neutralColSlabs h).card +
      (minRowSlabs h).card * (minColSlabs h).card +
      (maxRowSlabs h).card * (maxColSlabs h).card) :
    ∃ f : Matching h ≃ ↥(extrema h \ neutralSupport h),
      ∀ p, Matches h p (f p).val := by
  classical
  have hw (p : Matching h) : ∃ v : Cell m n, Matches h p v := by
    cases p with
    | inl p =>
      exact matching_slabs_min hh _ _
        (Finset.mem_product.mp p.property).1 (Finset.mem_product.mp p.property).2
    | inr p =>
      exact matching_slabs_max hh _ _
        (Finset.mem_product.mp p.property).1 (Finset.mem_product.mp p.property).2
  let f (p : Matching h) : Cell m n := Classical.choose (hw p)
  have hf (p : Matching h) : Matches h p (f p) := Classical.choose_spec (hw p)
  have hnot (p : Matching h) : f p ∉ neutralSupport h := by
    simp only [neutralSupport, Finset.mem_union, not_or]
    cases p with
    | inl p =>
      have hp := (Finset.mem_product.mp p.property)
      have hv := hf (.inl p)
      exact ⟨
        row_non_neutral hn _ (Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1).2
          1 (by norm_num) (Finset.mem_filter.mp hp.1).2.2 _ hv.1,
        col_non_neutral (by omega) _ (Finset.mem_filter.mp (Finset.mem_filter.mp hp.2).1).2
          1 (by norm_num) (Finset.mem_filter.mp hp.2).2.2 _ hv.2.1⟩
    | inr p =>
      have hp := (Finset.mem_product.mp p.property)
      have hv := hf (.inr p)
      exact ⟨
        row_non_neutral hn _ (Finset.mem_filter.mp (Finset.mem_filter.mp hp.1).1).2
          (-1) (by norm_num) (Finset.mem_filter.mp hp.1).2.2 _ hv.1,
        col_non_neutral (by omega) _ (Finset.mem_filter.mp (Finset.mem_filter.mp hp.2).1).2
          (-1) (by norm_num) (Finset.mem_filter.mp hp.2).2.2 _ hv.2.1⟩
  let F (p : Matching h) : ↥(extrema h \ neutralSupport h) :=
    ⟨f p, Finset.mem_sdiff.mpr ⟨by
      cases p with
      | inl p => exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (hf (.inl p)).2.2⟩
      | inr p => exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (hf (.inr p)).2.2⟩,
      hnot p⟩⟩
  have hinj : Function.Injective F := by
    intro p q he
    have hv : f p = f q := congrArg Subtype.val he
    cases p with
    | inl p =>
      cases q with
      | inl q =>
        apply congrArg Sum.inl; apply Subtype.ext; apply Prod.ext
        · exact row_slab_unique (Finset.mem_filter.mp (Finset.mem_filter.mp
            (Finset.mem_product.mp p.property).1).1).2
            (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_product.mp q.property).1).1).2
            _ (hf (.inl p)).1 (hv.symm ▸ (hf (.inl q)).1)
        · exact row_slab_unique (Finset.mem_filter.mp (Finset.mem_filter.mp
            (Finset.mem_product.mp p.property).2).1).2
            (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_product.mp q.property).2).1).2
            _ (hf (.inl p)).2.1 (hv.symm ▸ (hf (.inl q)).2.1)
      | inr q =>
        exact (minimum_maximum_distinct hm h _ _
          (hf (.inl p)).2.2 (hf (.inr q)).2.2 hv).elim
    | inr p =>
      cases q with
      | inl q =>
        exact (minimum_maximum_distinct hm h _ _
          (hf (.inl q)).2.2 (hf (.inr p)).2.2 hv.symm).elim
      | inr q =>
        apply congrArg Sum.inr; apply Subtype.ext; apply Prod.ext
        · exact row_slab_unique (Finset.mem_filter.mp (Finset.mem_filter.mp
            (Finset.mem_product.mp p.property).1).1).2
            (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_product.mp q.property).1).1).2
            _ (hf (.inr p)).1 (hv.symm ▸ (hf (.inr q)).1)
        · exact row_slab_unique (Finset.mem_filter.mp (Finset.mem_filter.mp
            (Finset.mem_product.mp p.property).2).1).2
            (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_product.mp q.property).2).1).2
            _ (hf (.inr p)).2.1 (hv.symm ▸ (hf (.inr q)).2.1)
  have hsub : neutralSupport h ⊆ extrema h := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv <;>
      obtain ⟨I, _, hi⟩ := Finset.mem_biUnion.mp hv <;>
      exact (Finset.mem_filter.mp hi).1
  have hcardn := neutral_slab_budget hh hm
  have hcardm := matching_slab_budget hh hm hn
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hce : Fintype.card (Matching h) = Fintype.card ↥(extrema h \ neutralSupport h) := by
    simp only [Matching, Fintype.card_sum, Fintype.card_coe, Finset.card_product]
    omega
  exact ⟨Equiv.ofBijective F ((Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj, hce⟩), hf⟩

/-- Equality classifies every actual extremum outside the neutral support by
its matching row and column types, including its minimum or maximum sign. -/
theorem equality_nonneutral_extremum {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n)
    (heq : (extrema h).card = (neutralRowSlabs h).card + (neutralColSlabs h).card +
      (minRowSlabs h).card * (minColSlabs h).card +
      (maxRowSlabs h).card * (maxColSlabs h).card)
    (v : Cell m n) (hv : v ∈ extrema h) (hvn : v ∉ neutralSupport h) :
    (∃ I ∈ minRowSlabs h, ∃ J ∈ minColSlabs h,
      I.Contains v.1 ∧ J.Contains v.2 ∧ IsStrictLocalMin h v) ∨
    (∃ I ∈ maxRowSlabs h, ∃ J ∈ maxColSlabs h,
      I.Contains v.1 ∧ J.Contains v.2 ∧ IsStrictLocalMax h v) := by
  classical
  obtain ⟨f, hf⟩ := matching_equiv hh hm hn heq
  obtain ⟨p, hp⟩ := f.surjective ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvn⟩⟩
  have hvp := hf p
  have he : (f p).val = v := congrArg Subtype.val hp
  rw [he] at hvp
  cases p with
  | inl p =>
    exact Or.inl ⟨p.val.1, (Finset.mem_product.mp p.property).1,
      p.val.2, (Finset.mem_product.mp p.property).2, hvp⟩
  | inr p =>
    exact Or.inr ⟨p.val.1, (Finset.mem_product.mp p.property).1,
      p.val.2, (Finset.mem_product.mp p.property).2, hvp⟩

end D5.S3.Combinatorics.Geometry.MiuraEqualitySaturation

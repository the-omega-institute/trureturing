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
import all D5.S3.Combinatorics.Geometry.MiuraSlabClassification
public import Mathlib.Data.Fintype.EquivFin

/-! Equality saturates the actual matching-cell injection. -/

@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraEqualitySaturation
open MiuraHeightEnvelope MiuraSlabExtrema MiuraSlabNeutral MiuraSlabIncidence
open MiuraSlabBudget MiuraSlabRunBound MiuraSlabCover MiuraSlabClassification
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

private theorem outside_neutral_of_outward {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n)
    (heq : (extrema h).card = (neutralRowSlabs h).card + (neutralColSlabs h).card +
      (minRowSlabs h).card * (minColSlabs h).card +
      (maxRowSlabs h).card * (maxColSlabs h).card)
    (I : Interval m) (hI : IsRowSlab h I) (t : ℤ) (ht : t ≠ 0)
    (hout : RowOutward h I t) (v : Cell m n) (hv : I.Contains v.1) :
    v ∉ neutralSupport h := by
  have hr := row_non_neutral hn I hI t ht hout v hv
  have hs := (slab_budget_equality hh hm hn heq).1
  simp only [neutralSupport, Finset.mem_union, not_or]
  exact ⟨hr, fun hc => hr (hs.symm ▸ hc)⟩

private theorem min_max_slab_distinct {h : Cell m n → ℤ} (hn : 0 < n)
    (I J : Interval m) (hI : I ∈ minRowSlabs h) (hJ : J ∈ maxRowSlabs h) : I ≠ J := by
  classical
  intro he; subst J
  have hp := (Finset.mem_filter.mp hI).2
  have hq := (Finset.mem_filter.mp hJ).2
  have he := outward_sign_unique hn I hp.1 1 (-1) hp.2 hq.2
  omega

/-- At equality, a minimum-type slab contains no ambient maximum and a
maximum-type slab contains no ambient minimum. No incidence is assumed. -/
theorem equality_slab_extrema_sign {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n)
    (heq : (extrema h).card = (neutralRowSlabs h).card + (neutralColSlabs h).card +
      (minRowSlabs h).card * (minColSlabs h).card +
      (maxRowSlabs h).card * (maxColSlabs h).card) :
    (∀ I ∈ minRowSlabs h, ∀ v : Cell m n, I.Contains v.1 → ¬ IsStrictLocalMax h v) ∧
    (∀ I ∈ maxRowSlabs h, ∀ v : Cell m n, I.Contains v.1 → ¬ IsStrictLocalMin h v) := by
  classical
  constructor
  · intro I hI v hv hmax
    have hsI := (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
    have hnot := outside_neutral_of_outward hh hm hn heq I hsI 1 (by norm_num)
      (Finset.mem_filter.mp hI).2.2 v hv
    have hev : v ∈ extrema h := by simp [extrema, hmax]
    rcases equality_nonneutral_extremum hh hm hn heq v hev hnot with
      ⟨J, hJ, K, hK, hvJ, hvK, hmin⟩ | ⟨J, hJ, K, hK, hvJ, hvK, _⟩
    · exact minimum_maximum_distinct hm h v v hmin hmax rfl
    · exact min_max_slab_distinct hn I J hI hJ
        (row_slab_unique hsI (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).2 v.1 hv hvJ)
  · intro I hI v hv hmin
    have hsI := (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
    have hnot := outside_neutral_of_outward hh hm hn heq I hsI (-1) (by norm_num)
      (Finset.mem_filter.mp hI).2.2 v hv
    have hev : v ∈ extrema h := by simp [extrema, hmin]
    rcases equality_nonneutral_extremum hh hm hn heq v hev hnot with
      ⟨J, hJ, K, hK, hvJ, hvK, _⟩ | ⟨J, hJ, K, hK, hvJ, hvK, hmax⟩
    · exact min_max_slab_distinct hn J I hJ hI
        (row_slab_unique (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).2 hsI v.1 hvJ hv)
    · exact minimum_maximum_distinct hm h v v hmin hmax rfl

/-- A maximum row slab has exactly one actual maximum when equality holds
and there is exactly one maximum column slab. -/
theorem equality_maximum_slab_unique {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n)
    (heq : (extrema h).card = (neutralRowSlabs h).card + (neutralColSlabs h).card +
      (minRowSlabs h).card * (minColSlabs h).card +
      (maxRowSlabs h).card * (maxColSlabs h).card)
    (hc : (maxColSlabs h).card = 1) (I : Interval m) (hI : I ∈ maxRowSlabs h) :
    ∃! v : Cell m n, I.Contains v.1 ∧ IsStrictLocalMax h v := by
  classical
  obtain ⟨J, hJset⟩ := Finset.card_eq_one.mp hc
  have hJ : J ∈ maxColSlabs h := by rw [hJset]; simp
  obtain ⟨f, hf⟩ := matching_equiv hh hm hn heq
  let p : ↥((maxRowSlabs h) ×ˢ (maxColSlabs h)) := ⟨(I, J), Finset.mem_product.mpr ⟨hI, hJ⟩⟩
  let v := (f (.inr p)).val
  have hv := hf (.inr p)
  refine ⟨v, ⟨hv.1, hv.2.2⟩, ?_⟩
  intro u hu
  have hsI := (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
  have hnot := outside_neutral_of_outward hh hm hn heq I hsI (-1) (by norm_num)
    (Finset.mem_filter.mp hI).2.2 u hu.1
  have heu : u ∈ extrema h := by simp [extrema, hu.2]
  obtain ⟨q, hq⟩ := f.surjective ⟨u, Finset.mem_sdiff.mpr ⟨heu, hnot⟩⟩
  have he : (f q).val = u := congrArg Subtype.val hq
  have hqu := hf q
  rw [he] at hqu
  cases q with
  | inl q => exact (minimum_maximum_distinct hm h u u hqu.2.2 hu.2 rfl).elim
  | inr q =>
    have hqr : q.val.1 = I := row_slab_unique
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_product.mp q.property).1).1).2
      hsI u.1 hqu.1 hu.1
    have hqc : q.val.2 = J := by
      have hcq := (Finset.mem_product.mp q.property).2
      exact Finset.mem_singleton.mp (hJset ▸ hcq)
    have hqp : q = p := Subtype.ext (Prod.ext hqr hqc)
    subst q
    exact he.symm

end D5.S3.Combinatorics.Geometry.MiuraEqualitySaturation

/- GID: D5/S3/Combinatorics/Geometry/MiuraSlabBudget
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraSlabBudget
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Actual slab types charge distinct ambient extremum cells. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraSlabIncidence

/-! Individual-edge counting for canonical occupied slabs of actual arrays. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraSlabBudget

open MiuraHeightEnvelope MiuraSlabExtrema MiuraSlabNeutral MiuraSlabIncidence

variable {m n : ℕ}

/-- Extrema incident with an actual neutral row slab. -/
noncomputable def rowNeutralSupport (h : Cell m n → ℤ) : Finset (Cell m n) :=
  (neutralRowSlabs h).biUnion (rowIncidences h)

/-- Extrema incident with an actual neutral column slab. -/
noncomputable def colNeutralSupport (h : Cell m n → ℤ) : Finset (Cell m n) :=
  (neutralColSlabs h).biUnion (colIncidences h)

/-- Every extremum with at least one neutral endpoint, counted as its own cell. -/
noncomputable def neutralSupport (h : Cell m n → ℤ) : Finset (Cell m n) :=
  rowNeutralSupport h ∪ colNeutralSupport h

/-- The double incidence count bounds the number of neutral slab vertices. -/
theorem neutral_slab_budget {h : Cell m n → ℤ} (hh : IsHeight h) (hm : 2 ≤ m) :
    (neutralRowSlabs h).card + (neutralColSlabs h).card ≤ (neutralSupport h).card := by
  classical
  have hr := neutral_rows_individual_count hh hm
  have hc := neutral_cols_individual_count hh hm
  have hra : (rowNeutralSupport h).card ≤ (neutralSupport h).card :=
    Finset.card_le_card Finset.subset_union_left
  have hca : (colNeutralSupport h).card ≤ (neutralSupport h).card :=
    Finset.card_le_card Finset.subset_union_right
  change 2 * (neutralRowSlabs h).card ≤ (rowNeutralSupport h).card at hr
  change 2 * (neutralColSlabs h).card ≤ (colNeutralSupport h).card at hc
  omega

/-- Under equality in the neutral charge, every neutral incidence joins two
neutral slabs: the two actual support sets coincide. -/
theorem neutral_budget_equality {h : Cell m n → ℤ} (hh : IsHeight h) (hm : 2 ≤ m)
    (heq : (neutralSupport h).card = (neutralRowSlabs h).card + (neutralColSlabs h).card) :
    rowNeutralSupport h = colNeutralSupport h ∧
    (neutralRowSlabs h).card = (neutralColSlabs h).card := by
  classical
  have hr := neutral_rows_individual_count hh hm
  have hc := neutral_cols_individual_count hh hm
  have hra : (rowNeutralSupport h).card ≤ (neutralSupport h).card :=
    Finset.card_le_card Finset.subset_union_left
  have hca : (colNeutralSupport h).card ≤ (neutralSupport h).card :=
    Finset.card_le_card Finset.subset_union_right
  change 2 * (neutralRowSlabs h).card ≤ (rowNeutralSupport h).card at hr
  change 2 * (neutralColSlabs h).card ≤ (colNeutralSupport h).card at hc
  have hre : (rowNeutralSupport h).card = (neutralSupport h).card := by omega
  have hce : (colNeutralSupport h).card = (neutralSupport h).card := by omega
  have hrset : rowNeutralSupport h = neutralSupport h :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
  have hcset : colNeutralSupport h = neutralSupport h :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
  exact ⟨hrset.trans hcset.symm, by omega⟩

private theorem row_non_neutral {h : Cell m n → ℤ} (hn : 0 < n)
    (I : Interval m) (hI : IsRowSlab h I) (t : ℤ) (ht : t ≠ 0)
    (hout : RowOutward h I t) (v : Cell m n) (hv : I.Contains v.1) :
    v ∉ rowNeutralSupport h := by
  classical
  intro hvn
  obtain ⟨J, hJ, hvJ⟩ := Finset.mem_biUnion.mp hvn
  obtain ⟨hJslab, s, hs, hcuts⟩ := Finset.mem_filter.mp hJ
  have hJ' : IsRowSlab h J := (Finset.mem_filter.mp hJslab).2
  have he : I = J := row_slab_unique hI hJ' v.1 hv (Finset.mem_filter.mp hvJ).2
  subst J
  exact neutral_not_outward hn I s t ht hcuts hout

private theorem col_non_neutral {h : Cell m n → ℤ} (hm : 0 < m)
    (J : Interval n) (hJ : IsRowSlab (transposeHeight h) J) (t : ℤ) (ht : t ≠ 0)
    (hout : RowOutward (transposeHeight h) J t) (v : Cell m n) (hv : J.Contains v.2) :
    v ∉ colNeutralSupport h := by
  classical
  intro hvn
  obtain ⟨I, hI, hvI⟩ := Finset.mem_biUnion.mp hvn
  obtain ⟨hIslab, s, hs, hcuts⟩ := Finset.mem_filter.mp hI
  have hI' : IsRowSlab (transposeHeight h) I := (Finset.mem_filter.mp hIslab).2
  have he : J = I := row_slab_unique hJ hI' v.2 hv (Finset.mem_filter.mp hvI).2
  subst I
  exact neutral_not_outward hm J s t ht hcuts hout

private theorem colOutward_of_transpose {h : Cell m n → ℤ} (J : Interval n) (t : ℤ)
    (hc : RowOutward (transposeHeight h) J t) : ColOutward h J t := by
  intro v u hv hu hadj
  exact hc (v.2, v.1) (u.2, u.1) hv hu (by
    simp only [adj, gdist] at hadj ⊢
    omega)

private theorem matching_slabs_min {h : Cell m n → ℤ} (hh : IsHeight h)
    (I : Interval m) (J : Interval n) (hI : I ∈ minRowSlabs h) (hJ : J ∈ minColSlabs h) :
    ∃ v : Cell m n, I.Contains v.1 ∧ J.Contains v.2 ∧ IsStrictLocalMin h v := by
  classical
  have hr := (Finset.mem_filter.mp hI).2.2
  have hc := (Finset.mem_filter.mp hJ).2.2
  obtain ⟨v, hv, hmin⟩ := matching_minimum hh I J hr (colOutward_of_transpose J 1 hc)
  have hv' : I.Contains v.1 ∧ J.Contains v.2 := by
    simpa only [rectangle, Finset.mem_product, Interval.mem_rows] using hv
  exact ⟨v, hv'.1, hv'.2, hmin⟩

private theorem matching_slabs_max {h : Cell m n → ℤ} (hh : IsHeight h)
    (I : Interval m) (J : Interval n) (hI : I ∈ maxRowSlabs h) (hJ : J ∈ maxColSlabs h) :
    ∃ v : Cell m n, I.Contains v.1 ∧ J.Contains v.2 ∧ IsStrictLocalMax h v := by
  classical
  have hr := (Finset.mem_filter.mp hI).2.2
  have hc := (Finset.mem_filter.mp hJ).2.2
  obtain ⟨v, hv, hmax⟩ := matching_maximum hh I J hr (colOutward_of_transpose J (-1) hc)
  have hv' : I.Contains v.1 ∧ J.Contains v.2 := by
    simpa only [rectangle, Finset.mem_product, Interval.mem_rows] using hv
  exact ⟨v, hv'.1, hv'.2, hmax⟩

private theorem minimum_maximum_distinct (hm : 2 ≤ m) (h : Cell m n → ℤ)
    (u v : Cell m n) (hu : IsStrictLocalMin h u) (hv : IsStrictLocalMax h v) : u ≠ v := by
  intro he
  subst v
  let i : Fin m := if u.1.val = 0 then ⟨1, by omega⟩ else ⟨u.1.val - 1, by have := u.1.isLt; omega⟩
  have hadj : adj u (i, u.2) := by
    dsimp [i]
    split <;> simp only [adj, gdist] <;> omega
  have := hu _ hadj
  have := hv _ hadj
  omega

/-- Each matching nonneutral rectangle contributes its own extremum outside
all neutral supports. Parallel extrema are not collapsed. -/
theorem matching_slab_budget {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) :
    (minRowSlabs h).card * (minColSlabs h).card +
      (maxRowSlabs h).card * (maxColSlabs h).card ≤
      ((extrema h) \ neutralSupport h).card := by
  classical
  let A := (minRowSlabs h) ×ˢ (minColSlabs h)
  let B := (maxRowSlabs h) ×ˢ (maxColSlabs h)
  have hA (p : A) : ∃ v : Cell m n,
      p.val.1.Contains v.1 ∧ p.val.2.Contains v.2 ∧ IsStrictLocalMin h v :=
    matching_slabs_min hh _ _ (Finset.mem_product.mp p.property).1 (Finset.mem_product.mp p.property).2
  have hB (p : B) : ∃ v : Cell m n,
      p.val.1.Contains v.1 ∧ p.val.2.Contains v.2 ∧ IsStrictLocalMax h v :=
    matching_slabs_max hh _ _ (Finset.mem_product.mp p.property).1 (Finset.mem_product.mp p.property).2
  let fA (p : A) : Cell m n := Classical.choose (hA p)
  let fB (p : B) : Cell m n := Classical.choose (hB p)
  have hfA (p : A) : p.val.1.Contains (fA p).1 ∧ p.val.2.Contains (fA p).2 ∧
      IsStrictLocalMin h (fA p) := Classical.choose_spec (hA p)
  have hfB (p : B) : p.val.1.Contains (fB p).1 ∧ p.val.2.Contains (fB p).2 ∧
      IsStrictLocalMax h (fB p) := Classical.choose_spec (hB p)
  have hnot (p : A) : fA p ∉ neutralSupport h := by
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp p.property
    have hr := row_non_neutral hn p.val.1 (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      1 (by norm_num) (Finset.mem_filter.mp hp).2.2 (fA p) (hfA p).1
    have hc := col_non_neutral (by omega : 0 < m) p.val.2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
      1 (by norm_num) (Finset.mem_filter.mp hq).2.2 (fA p) (hfA p).2.1
    simpa only [neutralSupport, Finset.mem_union, not_or] using And.intro hr hc
  have hnotB (p : B) : fB p ∉ neutralSupport h := by
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp p.property
    have hr := row_non_neutral hn p.val.1 (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      (-1) (by norm_num) (Finset.mem_filter.mp hp).2.2 (fB p) (hfB p).1
    have hc := col_non_neutral (by omega : 0 < m) p.val.2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
      (-1) (by norm_num) (Finset.mem_filter.mp hq).2.2 (fB p) (hfB p).2.1
    simpa only [neutralSupport, Finset.mem_union, not_or] using And.intro hr hc
  have hinjA : Function.Injective fA := by
    intro p q he
    apply Subtype.ext
    apply Prod.ext
    · have hp := (Finset.mem_product.mp p.property).1
      have hq := (Finset.mem_product.mp q.property).1
      exact row_slab_unique (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
        (fA p).1 (hfA p).1 (he.symm ▸ (hfA q).1)
    · have hp := (Finset.mem_product.mp p.property).2
      have hq := (Finset.mem_product.mp q.property).2
      exact row_slab_unique (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
        (fA p).2 (hfA p).2.1 (he.symm ▸ (hfA q).2.1)
  have hinjB : Function.Injective fB := by
    intro p q he
    apply Subtype.ext
    apply Prod.ext
    · have hp := (Finset.mem_product.mp p.property).1
      have hq := (Finset.mem_product.mp q.property).1
      exact row_slab_unique (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
        (fB p).1 (hfB p).1 (he.symm ▸ (hfB q).1)
    · have hp := (Finset.mem_product.mp p.property).2
      have hq := (Finset.mem_product.mp q.property).2
      exact row_slab_unique (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
        (fB p).2 (hfB p).2.1 (he.symm ▸ (hfB q).2.1)
  let F : A ⊕ B → ↥((extrema h) \ neutralSupport h) := fun p =>
    match p with
    | .inl p => ⟨fA p, Finset.mem_sdiff.mpr ⟨by simp [extrema, (hfA p).2.2], hnot p⟩⟩
    | .inr p => ⟨fB p, Finset.mem_sdiff.mpr ⟨by simp [extrema, (hfB p).2.2], hnotB p⟩⟩
  have hinj : Function.Injective F := by
    intro p q he
    have he' := congrArg Subtype.val he
    cases p with
    | inl p =>
      cases q with
      | inl q => exact congrArg Sum.inl (hinjA he')
      | inr q => exact (minimum_maximum_distinct hm h _ _ (hfA p).2.2 (hfB q).2.2 he').elim
    | inr p =>
      cases q with
      | inl q => exact (minimum_maximum_distinct hm h _ _ (hfA q).2.2 (hfB p).2.2 he'.symm).elim
      | inr q => exact congrArg Sum.inr (hinjB he')
  have hcard := Fintype.card_le_of_injective F hinj
  simpa only [Fintype.card_sum, Fintype.card_coe, A, B, Finset.card_product] using hcard

/-- The geometric charging bound on the canonical slabs of every actual array.
No independent incidence graph is supplied as a hypothesis. -/
theorem slab_extremum_budget {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) :
    (neutralRowSlabs h).card + (neutralColSlabs h).card +
      (minRowSlabs h).card * (minColSlabs h).card +
      (maxRowSlabs h).card * (maxColSlabs h).card ≤ (extrema h).card := by
  classical
  have hneutral := neutral_slab_budget hh hm
  have hmatching := matching_slab_budget hh hm hn
  have hsub : neutralSupport h ⊆ extrema h := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨I, hI, hvi⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_filter.mp hvi).1
    · obtain ⟨J, hJ, hvj⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_filter.mp hvj).1
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  omega


/-- Equality in the full geometric charge leaves no extremum with exactly one
neutral endpoint and forces equal numbers of neutral row and column slabs. -/
theorem slab_budget_equality {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n)
    (heq : (extrema h).card = (neutralRowSlabs h).card + (neutralColSlabs h).card +
      (minRowSlabs h).card * (minColSlabs h).card +
      (maxRowSlabs h).card * (maxColSlabs h).card) :
    rowNeutralSupport h = colNeutralSupport h ∧
    (neutralRowSlabs h).card = (neutralColSlabs h).card := by
  classical
  have hn' := neutral_slab_budget hh hm
  have hm' := matching_slab_budget hh hm hn
  have hsub : neutralSupport h ⊆ extrema h := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨I, hI, hvi⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_filter.mp hvi).1
    · obtain ⟨J, hJ, hvj⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_filter.mp hvj).1
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  apply neutral_budget_equality hh hm
  omega

end D5.S3.Combinatorics.Geometry.MiuraSlabBudget

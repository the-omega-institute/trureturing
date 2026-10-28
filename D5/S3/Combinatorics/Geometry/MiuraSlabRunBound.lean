/- GID: D5/S3/Combinatorics/Geometry/MiuraSlabRunBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraSlabRunBound
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Actual frozen row and column runs obey the geometric extremum bound. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraSlabSigns
public import D5.S3.Combinatorics.Geometry.MiuraSlabCover
public import D5.S3.Combinatorics.Geometry.MiuraSlabBudget

/-! The uniform individual-extremum bound on the same actual grid. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraSlabRunBound

open MiuraHeightEnvelope MiuraSlabExtrema MiuraSlabNeutral MiuraSlabIncidence
open MiuraSlabFrozen MiuraSlabClassification MiuraSlabSigns MiuraSlabCover MiuraSlabBudget

variable {m n : ℕ}

private theorem product_budget (r c : ℕ) (hr : 1 ≤ r) (hc : 1 ≤ c) :
    r + c ≤ r * c + 1 := by
  obtain ⟨r', hr'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  obtain ⟨c', hc'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : c ≠ 0)
  rw [hr', hc']
  nlinarith [Nat.zero_le (r' * c')]

/-- The number of actual row and column occupied slabs is at most the number
of individual extrema plus two whenever both axes have frozen rows. -/
theorem actual_slab_bound {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i)
    (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j) :
    (rowSlabs h).card + (rowSlabs (transposeHeight h)).card ≤ (extrema h).card + 2 := by
  have hpartR := row_slab_card_partition hh hm (by omega) hr
  have hpartC := row_slab_card_partition (transpose_isHeight hh) hn (by omega) hc
  have hminR := (minimum_row_slab_exists hh hm (by omega) hr).card_pos
  have hmaxR := (maximum_row_slab_exists hh hm (by omega) hr).card_pos
  have hminC := (minimum_row_slab_exists (transpose_isHeight hh) hn (by omega) hc).card_pos
  have hmaxC := (maximum_row_slab_exists (transpose_isHeight hh) hn (by omega) hc).card_pos
  have hproductMin := product_budget (minRowSlabs h).card (minColSlabs h).card (by omega) (by exact hminC)
  have hproductMax := product_budget (maxRowSlabs h).card (maxColSlabs h).card (by omega) (by exact hmaxC)
  have hbudget := slab_extremum_budget hh hm (by omega)
  change (rowSlabs (transposeHeight h)).card =
    (minColSlabs h).card + (maxColSlabs h).card + (neutralColSlabs h).card at hpartC
  omega

/-- An actual frozen run starts at an unoccupied row after an occupied row,
with the physical first row included in the definition. -/
def FrozenRowRunStart (h : Cell m n → ℤ) (i : Fin m) : Prop :=
  ¬ RowOccupied h i ∧ (i.val = 0 ∨ ∃ hi : 0 < i.val,
    RowOccupied h ⟨i.val - 1, by have := i.isLt; omega⟩)

noncomputable def frozenRowRunStarts (h : Cell m n → ℤ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (FrozenRowRunStart h)

/-- The exact occupied-slab and frozen-run count relation on an actual axis. -/
theorem slab_card_eq_frozen_runs_add_one {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 0 < n) :
    (rowSlabs h).card = (frozenRowRunStarts h).card + 1 := by
  classical
  let lastRow : Fin m := ⟨m - 1, by omega⟩
  obtain ⟨T, hTlast, hT⟩ := occupied_row_has_slab h lastRow (boundary_rows_occupied hh hm hn).2
  have hTend : T.last = lastRow := by
    apply Fin.ext
    have := T.last.isLt
    change T.first.val ≤ m - 1 ∧ m - 1 ≤ T.last.val at hTlast
    change T.last.val = m - 1
    omega
  let S := (rowSlabs h).filter (fun I => I.last.val + 1 < m)
  have hTmem : T ∈ rowSlabs h := by simp [rowSlabs, hT]
  have hTe : T ∉ S := by simp [S, hTend, lastRow]; omega
  have hsplit : rowSlabs h = insert T S := by
    ext I
    simp only [Finset.mem_insert]
    constructor
    · intro hI
      by_cases hi : I.last.val + 1 < m
      · right; exact Finset.mem_filter.mpr ⟨hI, hi⟩
      · left
        have hIlast : I.Contains lastRow := by
          change I.first.val ≤ m - 1 ∧ m - 1 ≤ I.last.val
          have := I.first.isLt
          have := I.last.isLt
          omega
        exact row_slab_unique (Finset.mem_filter.mp hI).2 hT lastRow hIlast hTlast
    · rintro (rfl | hI)
      · exact hTmem
      · exact (Finset.mem_filter.mp hI).1
  have hcard : S.card = (frozenRowRunStarts h).card := by
    apply Finset.card_bij (fun I hI => (⟨I.last.val + 1, (Finset.mem_filter.mp hI).2⟩ : Fin m))
    · intro I hI
      have hslab : IsRowSlab h I := (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
      simp only [frozenRowRunStarts, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hslab.2.2 _ rfl, Or.inr ⟨by change 0 < I.last.val + 1; omega, ?_⟩⟩
      have he : (⟨I.last.val + 1 - 1, by have := I.last.isLt; omega⟩ : Fin m) = I.last :=
        Fin.ext (by change I.last.val + 1 - 1 = I.last.val; omega)
      rw [he]
      exact hslab.1 I.last ⟨I.ordered, le_rfl⟩
    · intro I hI J hJ he
      have he' : I.last = J.last := Fin.ext (by
        have hv := congrArg Fin.val he
        change I.last.val + 1 = J.last.val + 1 at hv
        omega)
      have hsI := (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
      have hsJ := (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).2
      exact row_slab_unique hsI hsJ I.last ⟨I.ordered, le_rfl⟩ (he'.symm ▸ ⟨J.ordered, le_rfl⟩)
    · intro k hk
      have hstart : FrozenRowRunStart h k := (Finset.mem_filter.mp hk).2
      have hk0 : 0 < k.val := by
        by_contra hnot
        have he : k = (⟨0, by omega⟩ : Fin m) := Fin.ext (by change k.val = 0; omega)
        exact hstart.1 (he.symm ▸ (boundary_rows_occupied hh hm hn).1)
      have hprev : RowOccupied h (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin m) := by
        rcases hstart.2 with he | ⟨_, he⟩
        · omega
        · exact he
      obtain ⟨I, hiI, hI⟩ := occupied_row_has_slab h _ hprev
      have hlast : I.last.val + 1 = k.val := by
        have hi' : I.first.val ≤ k.val - 1 ∧ k.val - 1 ≤ I.last.val := hiI
        by_contra hne
        have hkI : I.Contains k := by
          change I.first.val ≤ k.val ∧ k.val ≤ I.last.val
          omega
        exact hstart.1 (hI.1 k hkI)
      have hIS : I ∈ S := by
        apply Finset.mem_filter.mpr
        exact ⟨by simp [rowSlabs, hI], by rw [hlast]; exact k.isLt⟩
      exact ⟨I, hIS, Fin.ext (by change I.last.val + 1 = k.val; exact hlast)⟩
  rw [hsplit, Finset.card_insert_of_notMem hTe, hcard]

/-- Every actual unit-edge array with frozen rows and columns has at least
as many individual extrema as the total number of frozen runs on both axes. -/
theorem frozen_runs_le_extrema {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i)
    (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j) :
    (frozenRowRunStarts h).card + (frozenRowRunStarts (transposeHeight h)).card ≤
      (extrema h).card := by
  have hbound := actual_slab_bound hh hm hn hr hc
  have hrow := slab_card_eq_frozen_runs_add_one hh hm (by omega)
  have hcol := slab_card_eq_frozen_runs_add_one (transpose_isHeight hh) hn (by omega)
  omega


/-- Equality in the actual run bound saturates the individual-incidence
charge and forces both matching-type product defects to vanish. -/
theorem frozen_run_equality_incidence {h : Cell m n → ℤ} (hh : IsHeight h)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hr : ∃ i, ¬ RowOccupied h i)
    (hc : ∃ j, ¬ RowOccupied (transposeHeight h) j)
    (heq : (extrema h).card = (frozenRowRunStarts h).card +
      (frozenRowRunStarts (transposeHeight h)).card) :
    rowNeutralSupport h = colNeutralSupport h ∧
    (neutralRowSlabs h).card = (neutralColSlabs h).card ∧
    ((minRowSlabs h).card - 1) * ((minColSlabs h).card - 1) = 0 ∧
    ((maxRowSlabs h).card - 1) * ((maxColSlabs h).card - 1) = 0 := by
  have hpartR := row_slab_card_partition hh hm (by omega) hr
  have hpartC := row_slab_card_partition (transpose_isHeight hh) hn (by omega) hc
  have hrow := slab_card_eq_frozen_runs_add_one hh hm (by omega)
  have hcol := slab_card_eq_frozen_runs_add_one (transpose_isHeight hh) hn (by omega)
  have hminR : 1 ≤ (minRowSlabs h).card := (minimum_row_slab_exists hh hm (by omega) hr).card_pos
  have hmaxR : 1 ≤ (maxRowSlabs h).card := (maximum_row_slab_exists hh hm (by omega) hr).card_pos
  have hminC : 1 ≤ (minColSlabs h).card :=
    (minimum_row_slab_exists (transpose_isHeight hh) hn (by omega) hc).card_pos
  have hmaxC : 1 ≤ (maxColSlabs h).card :=
    (maximum_row_slab_exists (transpose_isHeight hh) hn (by omega) hc).card_pos
  have hproductMin := product_budget (minRowSlabs h).card (minColSlabs h).card hminR hminC
  have hproductMax := product_budget (maxRowSlabs h).card (maxColSlabs h).card hmaxR hmaxC
  have hbudget := slab_extremum_budget hh hm (by omega)
  change (rowSlabs (transposeHeight h)).card =
    (minColSlabs h).card + (maxColSlabs h).card + (neutralColSlabs h).card at hpartC
  have heqBudget : (extrema h).card = (neutralRowSlabs h).card + (neutralColSlabs h).card +
      (minRowSlabs h).card * (minColSlabs h).card +
      (maxRowSlabs h).card * (maxColSlabs h).card := by omega
  have heqMin : (minRowSlabs h).card + (minColSlabs h).card =
      (minRowSlabs h).card * (minColSlabs h).card + 1 := by omega
  have heqMax : (maxRowSlabs h).card + (maxColSlabs h).card =
      (maxRowSlabs h).card * (maxColSlabs h).card + 1 := by omega
  obtain ⟨hsupport, hneutral⟩ := slab_budget_equality hh hm (by omega) heqBudget
  refine ⟨hsupport, hneutral, ?_, ?_⟩
  · have hr' := Nat.sub_add_cancel hminR
    have hc' := Nat.sub_add_cancel hminC
    nlinarith only [heqMin, hr', hc']
  · have hr' := Nat.sub_add_cancel hmaxR
    have hc' := Nat.sub_add_cancel hmaxC
    nlinarith only [heqMax, hr', hc']

end D5.S3.Combinatorics.Geometry.MiuraSlabRunBound

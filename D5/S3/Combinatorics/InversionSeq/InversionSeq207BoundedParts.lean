/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207BoundedParts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207BoundedParts
   mirror-E: none(waiver:formal-bounded-part-normalization)
   anchors: [mathlib/module/Mathlib.Combinatorics.Young.YoungDiagram]
   utility: none
   digest: Adjoining and removing a full row proves the bounded-part product formula. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Euler
import Mathlib.Combinatorics.Young.YoungDiagram

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207BoundedParts

theorem bounded_parts_normalization (width : ℕ) :
    (PowerSeries.mk fun area =>
      (({diagram : YoungDiagram | (∀ cell ∈ diagram, cell.2 < width) ∧
        diagram.cells.card = area} : Set YoungDiagram).ncard : ℚ)) *
      InversionSeq207Euler.eulerDenominator width = 1 := by
  classical
  let diagrams (bound area : ℕ) : Set YoungDiagram :=
    {diagram | (∀ cell ∈ diagram, cell.2 < bound) ∧ diagram.cells.card = area}
  let series (bound : ℕ) : PowerSeries ℚ :=
    PowerSeries.mk fun area => ((diagrams bound area).ncard : ℚ)
  have finite (bound area : ℕ) : (diagrams bound area).Finite := by
    apply Set.Finite.of_injOn (t :=
      ((Finset.range area ×ˢ Finset.range area).powerset : Set (Finset (ℕ × ℕ))))
      (f := YoungDiagram.cells) _ _ (Finset.finite_toSet _)
    · intro diagram hdiagram
      apply Finset.mem_powerset.mpr
      rintro ⟨row, column⟩ hcell
      have hrow : row < area := by
        have hsubset : (Finset.range (row + 1)).image (fun index => (index, column)) ⊆
            diagram.cells := by
          intro cell hmem
          rcases Finset.mem_image.mp hmem with ⟨index, hindex, rfl⟩
          exact diagram.up_left_mem (by simpa using Finset.mem_range.mp hindex)
            (by rfl) hcell
        have hcard := Finset.card_le_card hsubset
        rw [Finset.card_image_of_injective _
          (fun first second hequal => (Prod.mk.inj hequal).1), Finset.card_range,
          hdiagram.2] at hcard
        omega
      have hcolumn : column < area := by
        have hsubset : (Finset.range (column + 1)).image (fun index => (row, index)) ⊆
            diagram.cells := by
          intro cell hmem
          rcases Finset.mem_image.mp hmem with ⟨index, hindex, rfl⟩
          exact diagram.up_left_mem (by rfl)
            (by simpa using Finset.mem_range.mp hindex) hcell
        have hcard := Finset.card_le_card hsubset
        rw [Finset.card_image_of_injective _
          (fun first second hequal => (Prod.mk.inj hequal).2), Finset.card_range,
          hdiagram.2] at hcard
        omega
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hrow, Finset.mem_range.mpr hcolumn⟩
    · intro first _ second _ hequal
      exact YoungDiagram.ext hequal
  let tailCells (diagram : YoungDiagram) : Finset (ℕ × ℕ) :=
    (diagram.cells.filter fun cell => 0 < cell.1).image
      (fun cell => (cell.1 - 1, cell.2))
  have tailMem (diagram : YoungDiagram) (row column : ℕ) :
      (row, column) ∈ tailCells diagram ↔ (row + 1, column) ∈ diagram := by
    simp only [tailCells, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨earlierRow, earlierColumn⟩, ⟨hcell, hrow⟩, hequal⟩
      simp only [Prod.mk.injEq] at hequal
      have hearlierRow : earlierRow = row + 1 := by omega
      simpa only [hearlierRow, hequal.2, YoungDiagram.mem_cells] using hcell
    · intro hcell
      exact ⟨(row + 1, column), ⟨hcell, by omega⟩, by simp⟩
  let tail (diagram : YoungDiagram) : YoungDiagram :=
    { cells := tailCells diagram
      isLowerSet := by
        rintro ⟨lastRow, lastColumn⟩ ⟨firstRow, firstColumn⟩ hle hcell
        apply (tailMem _ _ _).mpr
        exact diagram.up_left_mem (Nat.add_le_add_right hle.1 1) hle.2
          ((tailMem _ _ _).mp hcell) }
  let raiseCells (bound : ℕ) (diagram : YoungDiagram) : Finset (ℕ × ℕ) :=
    ({0} ×ˢ Finset.range bound) ∪ diagram.cells.image
      (fun cell => (cell.1 + 1, cell.2))
  have raiseMem (bound : ℕ) (diagram : YoungDiagram) (row column : ℕ) :
      (row, column) ∈ raiseCells bound diagram ↔
        (row = 0 ∧ column < bound) ∨ (0 < row ∧ (row - 1, column) ∈ diagram) := by
    simp only [raiseCells, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_range, Finset.mem_image]
    constructor
    · rintro (hfirst | ⟨⟨earlierRow, earlierColumn⟩, hcell, hequal⟩)
      · exact Or.inl hfirst
      · simp only [Prod.mk.injEq] at hequal
        right
        refine ⟨by omega, ?_⟩
        have hrow : row - 1 = earlierRow := by omega
        simpa only [hrow, hequal.2, YoungDiagram.mem_cells] using hcell
    · rintro (hfirst | ⟨hrow, hcell⟩)
      · exact Or.inl hfirst
      · right
        exact ⟨(row - 1, column), hcell, by simp [Nat.sub_add_cancel (by omega : 1 ≤ row)]⟩
  let raise (bound : ℕ) (diagram : YoungDiagram)
      (hbound : ∀ cell ∈ diagram, cell.2 < bound) : YoungDiagram :=
    { cells := raiseCells bound diagram
      isLowerSet := by
        rintro ⟨lastRow, lastColumn⟩ ⟨firstRow, firstColumn⟩ hle hcell
        apply (raiseMem _ _ _ _).mpr
        rcases (raiseMem _ _ _ _).mp hcell with ⟨hlast, hcolumn⟩ | ⟨hlast, hcell⟩
        · left
          have hrowLe := hle.1
          exact ⟨by omega, lt_of_le_of_lt hle.2 hcolumn⟩
        · by_cases hfirst : firstRow = 0
          · left
            exact ⟨hfirst, lt_of_le_of_lt hle.2 (hbound (lastRow - 1, lastColumn) hcell)⟩
          · right
            exact ⟨by omega, diagram.up_left_mem (Nat.sub_le_sub_right hle.1 1)
              hle.2 hcell⟩ }
  have raiseCard (bound : ℕ) (diagram : YoungDiagram)
      (hbound : ∀ cell ∈ diagram, cell.2 < bound) :
      (raise bound diagram hbound).cells.card = bound + diagram.cells.card := by
    change (({0} ×ˢ Finset.range bound) ∪ diagram.cells.image
      (fun cell => (cell.1 + 1, cell.2))).card = _
    rw [Finset.card_union_of_disjoint]
    · have hinjective : Function.Injective (fun cell : ℕ × ℕ =>
          (cell.1 + 1, cell.2)) := by
        intro first second hequal
        apply Prod.ext
        · have hfirst := (Prod.mk.inj hequal).1
          omega
        · exact (Prod.mk.inj hequal).2
      rw [Finset.card_product, Finset.card_singleton, Finset.card_range,
        one_mul, Finset.card_image_of_injective _ hinjective]
    · apply Finset.disjoint_left.mpr
      intro cell hfirst hsecond
      rcases Finset.mem_product.mp hfirst with ⟨hrow, _⟩
      rcases Finset.mem_image.mp hsecond with ⟨earlier, _, hequal⟩
      have hzero := Finset.mem_singleton.mp hrow
      have hsucc := congrArg Prod.fst hequal
      simp only at hsucc
      omega
  have tailRaise (bound : ℕ) (diagram : YoungDiagram)
      (hbound : ∀ cell ∈ diagram, cell.2 < bound) :
      tail (raise bound diagram hbound) = diagram := by
    apply YoungDiagram.ext
    apply Finset.ext
    rintro ⟨row, column⟩
    change (row, column) ∈ tailCells _ ↔ (row, column) ∈ diagram
    rw [tailMem]
    change (row + 1, column) ∈ raiseCells _ _ ↔ _
    rw [raiseMem]
    simp
  have raiseTail (bound : ℕ) (diagram : YoungDiagram)
      (hbound : ∀ cell ∈ diagram, cell.2 < bound + 1)
      (hfull : (0, bound) ∈ diagram) :
      raise (bound + 1) (tail diagram)
        (fun cell hcell => hbound (cell.1 + 1, cell.2)
          ((tailMem _ _ _).mp hcell)) = diagram := by
    apply YoungDiagram.ext
    apply Finset.ext
    rintro ⟨row, column⟩
    change (row, column) ∈ raiseCells _ _ ↔ (row, column) ∈ diagram
    rw [raiseMem]
    constructor
    · rintro (⟨hrow, hcolumn⟩ | ⟨hrow, hcell⟩)
      · subst row
        exact diagram.up_left_mem (by rfl) (by omega) hfull
      · change (row - 1, column) ∈ tailCells diagram at hcell
        have hcell := (tailMem _ _ _).mp hcell
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ row)] using hcell
    · intro hcell
      by_cases hrow : row = 0
      · left
        exact ⟨hrow, hbound _ hcell⟩
      · right
        refine ⟨by omega, ?_⟩
        change (row - 1, column) ∈ tailCells diagram
        apply (tailMem _ _ _).mpr
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ row)] using hcell
  let full (bound area : ℕ) : Set YoungDiagram :=
    {diagram | diagram ∈ diagrams (bound + 1) area ∧ (0, bound) ∈ diagram}
  have fullArea (bound area : ℕ) (diagram : YoungDiagram) (hdiagram : diagram ∈
      full bound area) : area = bound + 1 + (tail diagram).cells.card := by
    have hcard := raiseCard (bound + 1) (tail diagram)
      (fun cell hcell => hdiagram.1.1 (cell.1 + 1, cell.2)
        ((tailMem _ _ _).mp hcell))
    rw [raiseTail bound diagram hdiagram.1.1 hdiagram.2, hdiagram.1.2] at hcard
    exact hcard
  have fullCard (bound area : ℕ) : (full bound area).ncard =
      if bound + 1 ≤ area then (diagrams (bound + 1) (area - (bound + 1))).ncard
      else 0 := by
    split_ifs with harea
    · apply Set.ncard_congr (fun diagram _ => tail diagram)
      · intro diagram hdiagram
        exact ⟨fun cell hcell => hdiagram.1.1 (cell.1 + 1, cell.2)
          ((tailMem _ _ _).mp hcell), by have hcard := fullArea _ _ _ hdiagram; omega⟩
      · intro first second hfirst hsecond hequal
        rw [← raiseTail bound first hfirst.1.1 hfirst.2,
          ← raiseTail bound second hsecond.1.1 hsecond.2]
        apply YoungDiagram.ext
        change raiseCells _ (tail first) = raiseCells _ (tail second)
        rw [hequal]
      · intro diagram hdiagram
        refine ⟨raise (bound + 1) diagram hdiagram.1, ?_,
          tailRaise (bound + 1) diagram hdiagram.1⟩
        constructor
        · constructor
          · rintro ⟨row, column⟩ hcell
            rcases (raiseMem _ _ _ _).mp hcell with ⟨_, hcolumn⟩ | ⟨_, hcell⟩
            · exact hcolumn
            · exact hdiagram.1 (row - 1, column) hcell
          · rw [raiseCard (bound + 1) diagram hdiagram.1, hdiagram.2]
            omega
        · apply (raiseMem _ _ _ _).mpr
          exact Or.inl ⟨rfl, by omega⟩
    · have hempty : full bound area = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro diagram hdiagram
        have hcard := fullArea _ _ _ hdiagram
        omega
      rw [hempty, Set.ncard_empty]
  have splitCard (bound area : ℕ) : (diagrams (bound + 1) area).ncard =
      (diagrams bound area).ncard + (full bound area).ncard := by
    have hsplit : diagrams (bound + 1) area = diagrams bound area ∪ full bound area := by
      ext diagram
      constructor
      · intro hdiagram
        by_cases hfull : (0, bound) ∈ diagram
        · exact Or.inr ⟨hdiagram, hfull⟩
        · left
          refine ⟨?_, hdiagram.2⟩
          intro cell hcell
          have hcolumn := hdiagram.1 cell hcell
          by_contra hlarge
          have hbad := diagram.up_left_mem (Nat.zero_le _)
            (by omega : bound ≤ cell.2) hcell
          exact hfull hbad
      · rintro (hdiagram | hdiagram)
        · exact ⟨fun cell hcell => lt_trans (hdiagram.1 cell hcell) (by omega),
            hdiagram.2⟩
        · exact hdiagram.1
    rw [hsplit]
    apply Set.ncard_union_eq _ (finite _ _) ((finite _ _).subset (fun _ h => h.1))
    apply Set.disjoint_left.mpr
    intro diagram hsmall hfull
    have hbad := hsmall.1 _ hfull.2
    omega
  have recurrence (bound : ℕ) :
      (1 - PowerSeries.X ^ (bound + 1)) * series (bound + 1) = series bound := by
    apply PowerSeries.ext
    intro area
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
    simp only [series, PowerSeries.coeff_mk]
    have hcard := splitCard bound area
    rw [fullCard] at hcard
    split_ifs with harea
    · rw [if_pos harea] at hcard
      have hcardQ : ((diagrams (bound + 1) area).ncard : ℚ) =
          (diagrams bound area).ncard +
            (diagrams (bound + 1) (area - (bound + 1))).ncard := by exact_mod_cast hcard
      linarith
    · rw [if_neg harea, add_zero] at hcard
      simp only [sub_zero]
      exact_mod_cast hcard
  have zeroSeries : series 0 = 1 := by
    have hdiagram (area : ℕ) : diagrams 0 area =
        if area = 0 then {⊥} else ∅ := by
      ext diagram
      have hempty (hbound : ∀ cell ∈ diagram, cell.2 < 0) : diagram = ⊥ := by
        apply YoungDiagram.ext
        apply Finset.ext
        intro cell
        simp only [YoungDiagram.cells_bot, Finset.notMem_empty, iff_false]
        exact fun hcell => Nat.not_lt_zero _ (hbound cell hcell)
      split_ifs with harea
      · subst area
        constructor
        · intro hmem
          exact Set.mem_singleton_iff.mpr (hempty hmem.1)
        · rintro rfl
          simp [diagrams]
      · constructor
        · intro hmem
          have hequal := hempty hmem.1
          have hcard := hmem.2
          rw [hequal, YoungDiagram.cells_bot, Finset.card_empty] at hcard
          exact harea hcard.symm
        · exact False.elim
    apply PowerSeries.ext
    intro area
    simp only [series, PowerSeries.coeff_mk, PowerSeries.coeff_one, hdiagram]
    split_ifs <;> simp
  change series width *
    (∏ part ∈ Finset.range width, (1 - PowerSeries.X ^ (part + 1))) = 1
  induction width with
  | zero => simpa only [Finset.range_zero, Finset.prod_empty, mul_one] using zeroSeries
  | succ width ih =>
      rw [Finset.prod_range_succ]
      calc
        series (width + 1) *
            ((∏ part ∈ Finset.range width, (1 - PowerSeries.X ^ (part + 1))) *
              (1 - PowerSeries.X ^ (width + 1))) =
            ((1 - PowerSeries.X ^ (width + 1)) * series (width + 1)) *
              (∏ part ∈ Finset.range width, (1 - PowerSeries.X ^ (part + 1))) := by ring
        _ = 1 := by rw [recurrence, ih]

end D5.S3.Combinatorics.InversionSeq.InversionSeq207BoundedParts

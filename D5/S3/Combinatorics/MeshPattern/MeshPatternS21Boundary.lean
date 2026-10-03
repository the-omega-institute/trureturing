/- GID: D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary
   mirror-E: none(waiver:coordinate-boundary-reconstruction)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic]
   utility: none
   digest: Coordinate-labelled boundaries recover their original cells by seven-state peeling. -/

import D5.S3.Combinatorics.MeshPattern.MeshPatternS21Peeling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MeshPattern.MeshPatternS21

def sevenBoundary (labels : ℕ → ℕ → SevenLabel) (column : ℕ) :
    List Bool → List (Bool × SevenLabel)
  | [] => []
  | false :: tail =>
    (false, labels column (tail.count false)) :: sevenBoundary labels column tail
  | true :: tail =>
    (true, labels (column + 1) (tail.count false)) ::
      sevenBoundary labels (column + 1) tail

noncomputable def sevenOutline (region : Set (ℕ × ℕ)) (bound column row : ℕ) :
    List Bool := by
  classical
  exact if row = 0 then [] else
    if column < bound ∧ (column + 1, row) ∈ region then
      true :: sevenOutline region bound (column + 1) row
    else false :: sevenOutline region bound column (row - 1)
termination_by bound - column + row
decreasing_by all_goals omega

def SevenLabel.transpose : SevenLabel → SevenLabel
  | .empty => .empty
  | .one => .one
  | .twoRow => .twoCol
  | .twoCol => .twoRow
  | .threeRow => .threeCol
  | .hook => .hook
  | .threeCol => .threeRow

theorem seven_active_outline (n : ℕ) (p : List ℕ)
    (hp : p.Perm (List.range' 1 n)) :
    let labels := fun x y => (sevenDiagram p x y).getD .empty
    let directions := sevenOutline (activeRegion n p) n 0 n
    directions.count false = n ∧
    (sevenCells 0 directions).Nodup ∧
    (∀ cell, cell ∈ sevenCells 0 directions ↔ cell ∈ activeRegion n p) ∧
    sevenPath .empty (sevenBoundary labels 0 directions) ∧
    (sevenBoundary labels 0 directions).foldl (fun _ step => step.2) .empty = .empty ∧
    (∀ cell ∈ sevenCells 0 directions,
      sevenInverse (labels cell.1 cell.2) (labels (cell.1 - 1) cell.2)
        (labels cell.1 (cell.2 - 1)) =
          some (labels (cell.1 - 1) (cell.2 - 1),
            decide (p.getD (cell.1 - 1) 0 = cell.2))) := by
  classical
  let region := activeRegion n p
  let labels := fun x y => (sevenDiagram p x y).getD SevenLabel.empty
  have hactive : ∀ maximum, maximum ∈ active n p ↔
      3 ≤ maximum ∧ maximum ≤ n ∧
      (rectangle p (n - maximum + 3) maximum).card = 3 := by
    intro maximum
    simp only [active, Finset.mem_filter, Finset.mem_range]
    omega
  have hsub : activeRegion n p ⊆ ferrersRegion n := by
    rintro ⟨x, y⟩ ⟨hx, hy, maximum, hmaximum, hxbound, hybound⟩
    have hbound := (hactive maximum).mp hmaximum
    exact ⟨maximum, hbound.1, hbound.2.1, hx, hxbound, hy, hybound⟩
  have hbounds : ∀ cell ∈ region,
      1 ≤ cell.1 ∧ cell.1 ≤ n ∧ 1 ≤ cell.2 ∧ cell.2 ≤ n := by
    intro cell hcell
    obtain ⟨maximum, hminimum, hmaximum, hfirst, hwidth, hsecond, hheight⟩ :=
      hsub hcell
    omega
  have hdown : ∀ x y smallerX smallerY, (x, y) ∈ region →
      1 ≤ smallerX → smallerX ≤ x → 1 ≤ smallerY → smallerY ≤ y →
      (smallerX, smallerY) ∈ region := by
    intro x y smallerX smallerY hmem hsmallX hboundX hsmallY hboundY
    obtain ⟨_, _, maximum, hmaximum, hxbound, hybound⟩ := hmem
    exact ⟨hsmallX, hsmallY, maximum, hmaximum,
      le_trans hboundX hxbound, le_trans hboundY hybound⟩
  have hrank : ∀ x y, x ≤ n → y ≤ n →
      x = 0 ∨ y = 0 ∨ (x, y) ∈ region → (rectangle p x y).card ≤ 3 := by
    intro x y hxlimit hylimit hvertex
    rcases hvertex with rfl | rfl | hmem
    · simp [rectangle]
    · have hzero : rectangle p x 0 = ∅ := by
        ext position
        simp only [rectangle, Finset.mem_filter, Finset.mem_range, Nat.le_zero,
          Finset.notMem_empty, iff_false, not_and]
        intro hposition hvalue
        have hlength : p.length = n := by simpa using hp.length_eq
        have hpositionbound : position < p.length := by omega
        have hmem := hp.mem_iff.mp (List.getElem_mem hpositionbound)
        rw [List.mem_range'_1] at hmem
        rw [List.getD_eq_getElem p 0 hpositionbound] at hvalue
        omega
      simp [hzero]
    · obtain ⟨_, _, maximum, hmaximum, hxbound, hybound⟩ := hmem
      have hsubset : rectangle p x y ⊆ rectangle p (n - maximum + 3) maximum := by
        intro position hposition
        simp only [rectangle, Finset.mem_filter, Finset.mem_range] at *
        exact ⟨lt_of_lt_of_le hposition.1 hxbound, le_trans hposition.2 hybound⟩
      have hcard := Finset.card_le_card hsubset
      simpa only [(hactive maximum).mp hmaximum |>.2.2] using hcard
  have hshape : ∀ column row, column ≤ n →
      let directions := sevenOutline region n column row
      directions.count false = row ∧
      (sevenCells column directions).Nodup ∧
      (∀ cell, cell ∈ sevenCells column directions ↔
        cell ∈ region ∧ column < cell.1 ∧ cell.2 ≤ row) := by
    have hinduct : ∀ fuel column row, column ≤ n → n - column + row = fuel →
        let directions := sevenOutline region n column row
        directions.count false = row ∧
        (sevenCells column directions).Nodup ∧
        (∀ cell, cell ∈ sevenCells column directions ↔
          cell ∈ region ∧ column < cell.1 ∧ cell.2 ≤ row) := by
      intro fuel
      induction fuel using Nat.strong_induction_on with
      | h fuel ih =>
        intro column row hcolumn hfuel
        by_cases hzero : row = 0
        · subst row
          rw [sevenOutline, if_pos rfl]
          simp only [List.count_nil, sevenCells]
          refine ⟨True.intro, List.nodup_nil, ?_⟩
          intro cell
          simp only [List.not_mem_nil, false_iff, not_and]
          intro hcell hfirst hsecond
          have := hbounds cell hcell
          omega
        · by_cases hstep : column < n ∧ (column + 1, row) ∈ region
          · have htail := ih (n - (column + 1) + row) (by omega)
              (column + 1) row (by omega) rfl
            obtain ⟨hcount, hnodup, hmem⟩ := htail
            rw [sevenOutline, if_neg hzero, if_pos hstep]
            simp only [sevenCells, hcount]
            have hstrip : ∀ cell,
                cell ∈ (List.range row).reverse.map (fun height =>
                  (column + 1, height + 1)) ↔
                cell.1 = column + 1 ∧ 1 ≤ cell.2 ∧ cell.2 ≤ row := by
              intro cell
              simp only [List.mem_map, List.mem_reverse, List.mem_range]
              constructor
              · rintro ⟨height, hheight, rfl⟩
                exact ⟨rfl, by omega, by omega⟩
              · rintro ⟨hfirst, hpositive, hheight⟩
                refine ⟨cell.2 - 1, by omega, ?_⟩
                exact Prod.ext (by simpa using hfirst.symm) (by omega)
            refine ⟨by simpa using hcount, ?_, ?_⟩
            · apply List.nodup_append.mpr
              refine ⟨hnodup, ?_, ?_⟩
              · apply List.Nodup.map _ (List.nodup_reverse.mpr List.nodup_range)
                intro left right heq
                have hsuccessor : left + 1 = right + 1 := congrArg Prod.snd heq
                omega
              · intro cell hleft other hright hequal
                subst other
                have := (hmem cell).mp hleft
                have := (hstrip cell).mp hright
                omega
            · intro cell
              rw [List.mem_append, hmem, hstrip]
              constructor
              · rintro (⟨hcell, hfirst, hsecond⟩ | ⟨hfirst, hpositive, hsecond⟩)
                · exact ⟨hcell, by omega, hsecond⟩
                · refine ⟨?_, by omega, hsecond⟩
                  have := hdown (column + 1) row (column + 1) cell.2 hstep.2
                    (by omega) (by omega) hpositive hsecond
                  convert this using 1
                  exact Prod.ext hfirst rfl
              · rintro ⟨hcell, hfirst, hsecond⟩
                by_cases hfar : column + 1 < cell.1
                · exact Or.inl ⟨hcell, hfar, hsecond⟩
                · exact Or.inr ⟨by omega, (hbounds cell hcell).2.2.1, hsecond⟩
          · have htail := ih (n - column + (row - 1)) (by omega)
              column (row - 1) hcolumn rfl
            obtain ⟨hcount, hnodup, hmem⟩ := htail
            rw [sevenOutline, if_neg hzero, if_neg hstep]
            simp only [sevenCells]
            refine ⟨?_, hnodup, ?_⟩
            · simp only [List.count_cons_self, hcount]
              omega
            intro cell
            rw [hmem]
            constructor
            · rintro ⟨hcell, hfirst, hsecond⟩
              exact ⟨hcell, hfirst, by omega⟩
            · rintro ⟨hcell, hfirst, hsecond⟩
              refine ⟨hcell, hfirst, ?_⟩
              have hstrict : cell.2 < row := by
                by_contra hnot
                have hequal : cell.2 = row := by omega
                have hbound := hbounds cell hcell
                have hcontained := hdown cell.1 cell.2 (column + 1) row hcell
                  (by omega) (by omega) (by omega) (by omega)
                exact hstep ⟨by omega, hcontained⟩
              omega
    intro column row hcolumn
    exact hinduct (n - column + row) column row hcolumn rfl
  have hlabel : ∀ x y, x ≤ n → y ≤ n →
      x = 0 ∨ y = 0 ∨ (x, y) ∈ region →
      sevenDiagram p x y = some (labels x y) ∧
        (∀ west, sevenDiagram p (x - 1) y = some west →
          sevenEdge west (labels x y) = true) ∧
        (∀ south, sevenDiagram p x (y - 1) = some south →
          sevenEdge south (labels x y) = true) := by
    intro x y hx hy hvertex
    obtain ⟨label, hcomputed, hsize, hwest, hsouth⟩ :=
      seven_state_construction n p hp x hx y hy (hrank x y hx hy hvertex)
    have hequal : labels x y = label := by simp [labels, hcomputed]
    subst label
    exact ⟨hcomputed, hwest, hsouth⟩
  have hpath : ∀ column row, column ≤ n → row ≤ n →
      column = 0 ∨ row = 0 ∨ (column, row) ∈ region →
      sevenPath (labels column row)
        (sevenBoundary labels column (sevenOutline region n column row)) := by
    have hinduct : ∀ fuel column row, column ≤ n → row ≤ n →
        column = 0 ∨ row = 0 ∨ (column, row) ∈ region →
        n - column + row = fuel →
        sevenPath (labels column row)
          (sevenBoundary labels column (sevenOutline region n column row)) := by
      intro fuel
      induction fuel using Nat.strong_induction_on with
      | h fuel ih =>
        intro column row hcolumn hrow hvertex hfuel
        by_cases hzero : row = 0
        · rw [sevenOutline, if_pos hzero]
          trivial
        · by_cases hstep : column < n ∧ (column + 1, row) ∈ region
          · have htail := ih (n - (column + 1) + row) (by omega)
              (column + 1) row (by omega) hrow (Or.inr (Or.inr hstep.2)) rfl
            have hcount := (hshape (column + 1) row (by omega)).1
            have hsource := (hlabel column row hcolumn hrow hvertex).1
            have hedge := (hlabel (column + 1) row (by omega) hrow
              (Or.inr (Or.inr hstep.2))).2.1 (labels column row) (by simpa using hsource)
            rw [sevenOutline, if_neg hzero, if_pos hstep]
            simpa [sevenBoundary, sevenPath, hcount]
              using And.intro hedge htail
          · have hnext : column = 0 ∨ row - 1 = 0 ∨ (column, row - 1) ∈ region := by
              rcases hvertex with haxis | haxis | hcell
              · exact Or.inl haxis
              · exact False.elim (hzero haxis)
              · by_cases hbottom : row - 1 = 0
                · exact Or.inr (Or.inl hbottom)
                · exact Or.inr (Or.inr (hdown column row column (row - 1) hcell
                    (hbounds _ hcell).1 (by omega) (by omega) (by omega)))
            have htail := ih (n - column + (row - 1)) (by omega)
              column (row - 1) hcolumn (by omega) hnext rfl
            have hcount := (hshape column (row - 1) hcolumn).1
            have hsource := (hlabel column (row - 1) hcolumn (by omega) hnext).1
            have hedge := (hlabel column row hcolumn hrow hvertex).2.2
              (labels column (row - 1)) hsource
            rw [sevenOutline, if_neg hzero, if_neg hstep]
            simpa [sevenBoundary, sevenPath, hcount]
              using And.intro hedge htail
    intro column row hcolumn hrow hvertex
    exact hinduct (n - column + row) column row hcolumn hrow hvertex rfl
  have hterminal : ∀ directions : List Bool, ∀ column,
      (sevenBoundary labels column directions).foldl (fun _ step => step.2)
          (labels column (directions.count false)) =
        labels (column + directions.count true) 0 := by
    intro directions
    induction directions with
    | nil => intro column; simp [sevenBoundary]
    | cons direction tail ih =>
      intro column
      cases direction <;>
        simp [sevenBoundary, ih, Nat.add_comm, Nat.add_left_comm]
  let directions := sevenOutline region n 0 n
  have hshapeMain := hshape 0 n (by omega)
  have hstart : labels 0 n = .empty := by simp [labels, sevenDiagram]
  have hpathMain : sevenPath .empty (sevenBoundary labels 0 directions) := by
    simpa [hstart] using hpath 0 n (by omega) (by omega) (Or.inl rfl)
  have hterminalMain :
      (sevenBoundary labels 0 directions).foldl (fun _ step => step.2) .empty = .empty := by
    have := hterminal directions 0
    rw [hshapeMain.1, hstart] at this
    have haxis : ∀ x, labels x 0 = .empty := by
      intro x
      cases x <;> simp [labels, sevenDiagram]
    simpa only [haxis] using this
  have hinverse : ∀ southwest northwest southeast northeast : SevenLabel,
      ∀ entry : Bool, sevenForward southwest northwest southeast entry = some northeast →
        sevenInverse northeast northwest southeast = some (southwest, entry) := by
    intro southwest northwest southeast northeast entry hforward
    have := List.find?_some hforward
    simpa [sevenForward] using this
  have hlocal : ∀ cell ∈ sevenCells 0 directions,
      sevenInverse (labels cell.1 cell.2) (labels (cell.1 - 1) cell.2)
        (labels cell.1 (cell.2 - 1)) =
          some (labels (cell.1 - 1) (cell.2 - 1),
            decide (p.getD (cell.1 - 1) 0 = cell.2)) := by
    intro cell hcell
    have hregion := ((hshapeMain.2.2 cell).mp hcell).1
    obtain ⟨hxpositive, hx, hypositive, hy⟩ := hbounds cell hregion
    have hsmaller : ∀ x y, x ≤ cell.1 → y ≤ cell.2 →
        x = 0 ∨ y = 0 ∨ (x, y) ∈ region := by
      intro x y hfirst hsecond
      by_cases hxzero : x = 0
      · exact Or.inl hxzero
      by_cases hyzero : y = 0
      · exact Or.inr (Or.inl hyzero)
      exact Or.inr (Or.inr (hdown cell.1 cell.2 x y hregion
        (by omega) hfirst (by omega) hsecond))
    have hne := (hlabel cell.1 cell.2 hx hy (hsmaller _ _ (by omega) (by omega))).1
    have hnw := (hlabel (cell.1 - 1) cell.2 (by omega) hy
      (hsmaller _ _ (by omega) (by omega))).1
    have hse := (hlabel cell.1 (cell.2 - 1) hx (by omega)
      (hsmaller _ _ (by omega) (by omega))).1
    have hsw := (hlabel (cell.1 - 1) (cell.2 - 1) (by omega) (by omega)
      (hsmaller _ _ (by omega) (by omega))).1
    have hxsucc : cell.1 = cell.1 - 1 + 1 := by omega
    have hysucc : cell.2 = cell.2 - 1 + 1 := by omega
    have hforward :
        sevenForward (labels (cell.1 - 1) (cell.2 - 1))
          (labels (cell.1 - 1) cell.2) (labels cell.1 (cell.2 - 1))
          (decide (p.getD (cell.1 - 1) 0 = cell.2)) = some (labels cell.1 cell.2) := by
      conv_lhs at hne => rw [hxsucc, hysucc, sevenDiagram]
      simpa only [← hxsucc, ← hysucc, hsw, hnw, hse,
        Option.bind_some, pure, bind] using hne
    exact hinverse _ _ _ _ _ hforward
  refine ⟨hshapeMain.1, hshapeMain.2.1, ?_, hpathMain, hterminalMain, hlocal⟩
  intro cell
  rw [hshapeMain.2.2 cell]
  constructor
  · exact And.left
  · intro hcell
    have := hbounds cell hcell
    exact ⟨hcell, by omega, by omega⟩

theorem seven_corner_boundary (n : ℕ) (p : List ℕ)
    (maximum : ℕ) (hmaximum : maximum ∈ active n p) :
    ∃ beforePath afterPath : List Bool,
      sevenOutline (activeRegion n p) n 0 n = beforePath ++ true :: afterPath ∧
      beforePath.count true + 1 = n - maximum + 3 ∧ afterPath.count false = maximum := by
  classical
  let region := activeRegion n p
  let width := n - maximum + 3
  have hmaximumBounds : 3 ≤ maximum ∧ maximum ≤ n := by
    have := Finset.mem_filter.mp hmaximum
    have := Finset.mem_range.mp this.1
    dsimp only [active] at hmaximum
    simp only [Finset.mem_filter, Finset.mem_range] at hmaximum
    omega
  have hwidth : 1 ≤ width ∧ width ≤ n := by dsimp only [width]; omega
  have hactive : ∀ maximum, maximum ∈ active n p ↔
      3 ≤ maximum ∧ maximum ≤ n ∧
      (rectangle p (n - maximum + 3) maximum).card = 3 := by
    intro maximum
    simp only [active, Finset.mem_filter, Finset.mem_range]
    omega
  have hcorner : (width, maximum) ∈ region ∧
      (width + 1, maximum) ∉ region ∧ (width, maximum + 1) ∉ region := by
    refine ⟨⟨by omega, by omega, maximum, hmaximum, le_refl _, le_refl _⟩, ?_, ?_⟩
    · rintro ⟨_, _, other, hother, hx, hy⟩
      have hotherbound := (hactive other).mp hother
      dsimp only [width] at hx
      omega
    · rintro ⟨_, _, other, hother, hx, hy⟩
      have hotherbound := (hactive other).mp hother
      dsimp only [width] at hx
      omega
  have hdown : ∀ x y smallerX smallerY, (x, y) ∈ region →
      1 ≤ smallerX → smallerX ≤ x → 1 ≤ smallerY → smallerY ≤ y →
      (smallerX, smallerY) ∈ region := by
    intro x y smallerX smallerY hmem hsmallX hboundX hsmallY hboundY
    obtain ⟨_, _, maximum, hmaximum, hxbound, hybound⟩ := hmem
    exact ⟨hsmallX, hsmallY, maximum, hmaximum,
      le_trans hboundX hxbound, le_trans hboundY hybound⟩
  have hheight : ∀ column row, column ≤ n →
      (sevenOutline region n column row).count false = row := by
    have hinduct : ∀ fuel column row, n - column + row = fuel → column ≤ n →
        (sevenOutline region n column row).count false = row := by
      intro fuel
      induction fuel using Nat.strong_induction_on with
      | h fuel ih =>
        intro column row hfuel hcolumn
        by_cases hzero : row = 0
        · subst row
          rw [sevenOutline, if_pos rfl]
          rfl
        · by_cases hstep : column < n ∧ (column + 1, row) ∈ region
          · have htail := ih (n - (column + 1) + row) (by omega)
              (column + 1) row rfl (by omega)
            rw [sevenOutline, if_neg hzero, if_pos hstep]
            simpa only [List.count_cons, beq_iff_eq, Bool.true_eq_false, ↓reduceIte,
              Nat.add_zero] using htail
          · have htail := ih (n - column + (row - 1)) (by omega)
              column (row - 1) rfl hcolumn
            rw [sevenOutline, if_neg hzero, if_neg hstep]
            simp only [List.count_cons, beq_self_eq_true, ↓reduceIte, htail]
            omega
    intro column row hcolumn
    exact hinduct (n - column + row) column row rfl hcolumn
  have hinduct : ∀ fuel column row, n - column + row = fuel → column < width →
      maximum ≤ row → row ≤ n →
      ∃ beforePath afterPath : List Bool,
        sevenOutline region n column row = beforePath ++ true :: afterPath ∧
        column + beforePath.count true + 1 = width ∧ afterPath.count false = maximum := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro column row hfuel hcolumn hrow hrowBound
      have hzero : row ≠ 0 := by omega
      by_cases hstep : column < n ∧ (column + 1, row) ∈ region
      · by_cases htarget : column + 1 = width
        · have hrowEqual : row = maximum := by
            by_contra hne
            have hupper : (width, maximum + 1) ∈ region :=
              hdown (column + 1) row width (maximum + 1) hstep.2 hwidth.1
                (by omega) (by omega) (by omega)
            exact hcorner.2.2 hupper
          refine ⟨[], sevenOutline region n (column + 1) row, ?_, ?_, ?_⟩
          · rw [sevenOutline, if_neg hzero, if_pos hstep]
            rfl
          · simpa only [List.count_nil, Nat.add_zero] using htarget
          · rw [hheight (column + 1) row (by omega), hrowEqual]
        · obtain ⟨beforePath, afterPath, hshape, hprefix, hsuffix⟩ :=
            ih (n - (column + 1) + row) (by omega) (column + 1) row rfl
              (by omega) hrow hrowBound
          refine ⟨true :: beforePath, afterPath, ?_, ?_, hsuffix⟩
          · rw [sevenOutline, if_neg hzero, if_pos hstep, hshape]
            rfl
          · simp only [List.count_cons, beq_self_eq_true, ↓reduceIte]
            omega
      · have hstrictRow : maximum < row := by
          by_contra hnot
          have hrowEqual : row = maximum := by omega
          have hnext : (column + 1, row) ∈ region := hdown width maximum
            (column + 1) row hcorner.1 (by omega) (by omega) (by omega) (by omega)
          exact hstep ⟨by omega, hnext⟩
        obtain ⟨beforePath, afterPath, hshape, hprefix, hsuffix⟩ :=
          ih (n - column + (row - 1)) (by omega) column (row - 1) rfl
            hcolumn (by omega) (by omega)
        refine ⟨false :: beforePath, afterPath, ?_, ?_, hsuffix⟩
        · rw [sevenOutline, if_neg hzero, if_neg hstep, hshape]
          rfl
        · simpa using hprefix
  simpa only [Nat.zero_add] using hinduct (n + n) 0 n (by omega)
    (by omega) hmaximumBounds.2 (by omega)

end D5.S3.Combinatorics.MeshPattern.MeshPatternS21

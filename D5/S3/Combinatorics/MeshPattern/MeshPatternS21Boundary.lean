/- GID: D5/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/MeshPatternS21Boundary
   mirror-E: none(waiver:coordinate-boundary-reconstruction)
   anchors: [mathlib/module/Mathlib.Data.List.OfFn]
   utility: none
   digest: Coordinate-labelled boundaries recover their original cells by seven-state peeling. -/

import D5.S3.Combinatorics.MeshPattern.MeshPatternS21Peeling
import Mathlib.Data.List.OfFn

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

def sevenCells (column : ℕ) : List Bool → List (ℕ × ℕ)
  | [] => []
  | false :: tail => sevenCells column tail
  | true :: tail => sevenCells (column + 1) tail ++
    (List.range (tail.count false)).reverse.map (fun row => (column + 1, row + 1))

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

theorem seven_forward_peeling (labels : ℕ → ℕ → SevenLabel)
    (entries : ℕ → ℕ → Bool) (column : ℕ) (directions : List Bool)
    (hlocal : ∀ cell ∈ sevenCells column directions,
      sevenInverse (labels cell.1 cell.2) (labels (cell.1 - 1) cell.2)
        (labels cell.1 (cell.2 - 1)) =
          some (labels (cell.1 - 1) (cell.2 - 1), entries cell.1 cell.2)) :
    sevenPeel (labels column (directions.count false)) column
        (sevenBoundary labels column directions) =
      some (sevenBoundary labels column
        (List.replicate (directions.count false) false ++
          List.replicate (directions.count true) true),
        (sevenCells column directions).map (fun cell =>
          (cell.1, cell.2, entries cell.1 cell.2))) := by
  have hshape : ∀ directions : List Bool, ∀ column,
      (sevenBoundary labels column directions).map Prod.fst = directions := by
    intro directions
    induction directions with
    | nil => intro column; rfl
    | cons direction tail ih =>
      intro column
      cases direction <;> simp [sevenBoundary, ih]
  have hslide : ∀ height width column,
      (∀ row < height,
        sevenInverse (labels (column + 1) (row + 1)) (labels column (row + 1))
          (labels (column + 1) row) =
            some (labels column row, entries (column + 1) (row + 1))) →
      sevenSlide column (labels column height) (labels (column + 1) height)
          (sevenBoundary labels (column + 1)
            (List.replicate height false ++ List.replicate width true)) =
        some (sevenBoundary labels column
          (List.replicate height false ++ List.replicate (width + 1) true),
          (List.range height).reverse.map (fun row =>
            (column + 1, row + 1, entries (column + 1) (row + 1)))) := by
    intro height
    induction height with
    | zero =>
      intro width column hlocal
      cases width <;>
        simp [sevenBoundary, sevenSlide, List.replicate_succ, List.count_replicate]
    | succ height ih =>
      intro width column hlocal
      have hstep := hlocal height (by omega)
      have htail := ih width column (fun row hrow => hlocal row (by omega))
      simp [List.replicate_succ, sevenBoundary, sevenSlide, hstep, htail,
        hshape, List.range_succ, List.reverse_append, List.count_replicate]
  induction directions generalizing column with
  | nil => simp [sevenBoundary, sevenPeel, sevenCells]
  | cons direction tail ih =>
    cases direction with
    | false =>
      have htail := ih column (by simpa [sevenCells] using hlocal)
      simp [sevenBoundary, sevenCells, sevenPeel, htail,
        List.replicate_succ, List.count_replicate]
    | true =>
      have htail := ih (column + 1) (by
        intro cell hcell
        exact hlocal cell (by simp [sevenCells, hcell]))
      have hstrip := hslide (tail.count false) (tail.count true) column (by
        intro row hrow
        have hcell := hlocal (column + 1, row + 1) (by
          simp only [sevenCells, List.mem_append, List.mem_map, List.mem_reverse,
            List.mem_range]
          exact Or.inr ⟨row, hrow, rfl⟩)
        simpa using hcell)
      simp [sevenBoundary, sevenCells, sevenPeel, htail, hstrip,
        List.map_map, List.replicate_succ]

open scoped Classical in
theorem seven_active_boundary (n : ℕ) (p : List ℕ)
    (hp : p.Perm (List.range' 1 n)) :
    let labels := fun x y => (sevenDiagram p x y).getD .empty
    let directions := sevenOutline (activeRegion n p) n 0 n
    directions.count false = n ∧
    (sevenCells 0 directions).Nodup ∧
    (∀ cell, cell ∈ sevenCells 0 directions ↔ cell ∈ activeRegion n p) ∧
    sevenPath .empty (sevenBoundary labels 0 directions) ∧
    ∃ axes, sevenPeel .empty 0 (sevenBoundary labels 0 directions) =
      some (axes, (sevenCells 0 directions).map (fun cell =>
        (cell.1, cell.2, decide (p.getD (cell.1 - 1) 0 = cell.2)))) ∧
      ∀ step ∈ axes, step.2 = .empty := by
  classical
  let region := activeRegion n p
  let labels := fun x y => (sevenDiagram p x y).getD SevenLabel.empty
  have hgeometry := active_geometry n p hp
  have hbounds : ∀ cell ∈ region,
      1 ≤ cell.1 ∧ cell.1 ≤ n ∧ 1 ≤ cell.2 ∧ cell.2 ≤ n := by
    intro cell hcell
    obtain ⟨maximum, hminimum, hmaximum, hfirst, hwidth, hsecond, hheight⟩ :=
      hgeometry.1 hcell
    omega
  have hdown : ∀ x y smallerX smallerY, (x, y) ∈ region →
      1 ≤ smallerX → smallerX ≤ x → 1 ≤ smallerY → smallerY ≤ y →
      (smallerX, smallerY) ∈ region := hgeometry.2.1
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
      seven_state_construction n p hp x hx y hy (hgeometry.2.2.1 x y hx hy hvertex)
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
  have hcomputed := seven_forward_peeling labels
    (fun x y => decide (p.getD (x - 1) 0 = y)) 0 directions hlocal
  obtain ⟨axes, cells, hpeel, haxes, hsorted, hperm, hlast, hempty⟩ :=
    seven_boundary_peeling .empty 0 (sevenBoundary labels 0 directions) hpathMain
  have hequal : cells = (sevenCells 0 directions).map (fun cell =>
      (cell.1, cell.2, decide (p.getD (cell.1 - 1) 0 = cell.2))) := by
    rw [hshapeMain.1, hstart, hpeel] at hcomputed
    exact congrArg Prod.snd (Option.some.inj hcomputed)
  refine ⟨hshapeMain.1, hshapeMain.2.1, ?_, hpathMain, axes, ?_, ?_⟩
  · intro cell
    rw [hshapeMain.2.2 cell]
    constructor
    · exact And.left
    · intro hcell
      have := hbounds cell hcell
      exact ⟨hcell, by omega, by omega⟩
  · simpa [hequal] using hpeel
  · exact hempty rfl hterminalMain

theorem seven_conjugated_reconstruction (column : ℕ)
    (boundary : List (Bool × SevenLabel)) (hboundary : sevenPath .empty boundary)
    (hterminal : boundary.foldl (fun _ step => step.2) .empty = .empty) :
    let conjugate := boundary.map (fun step => (step.1, step.2.transpose))
    ∃ (axes : List (Bool × SevenLabel)) (left right : List (ℕ × ℕ × Bool)),
      sevenPeel .empty column boundary = some (axes, left) ∧
      sevenPeel .empty column conjugate = some (axes, right) ∧
      left.map (fun cell => (cell.1, cell.2.1)) =
        sevenCells column (boundary.map Prod.fst) ∧
      right.map (fun cell => (cell.1, cell.2.1)) =
        sevenCells column (boundary.map Prod.fst) ∧
      (∀ row, left.countP (fun cell => cell.2.1 == row && cell.2.2) =
        right.countP (fun cell => cell.2.1 == row && cell.2.2)) ∧
      (∀ target, left.countP (fun cell => cell.1 == target && cell.2.2) =
        right.countP (fun cell => cell.1 == target && cell.2.2)) ∧
      (∀ row, right.countP (fun cell => cell.2.1 == row && cell.2.2) ≤ 1) ∧
      (∀ target, right.countP (fun cell => cell.1 == target && cell.2.2) ≤ 1) ∧
      (∀ step ∈ axes, step.2 = .empty) := by
  let conjugate := fun path : List (Bool × SevenLabel) =>
    path.map (fun step => (step.1, step.2.transpose))
  have hgrade : ∀ label : SevenLabel, label.transpose.size = label.size := by
    intro label
    cases label <;> rfl
  have hedge : ∀ smaller larger : SevenLabel,
      sevenEdge smaller.transpose larger.transpose = sevenEdge smaller larger := by
    intro smaller larger
    cases smaller <;> cases larger <;> rfl
  have hshape : ∀ path, (conjugate path).map Prod.fst = path.map Prod.fst := by
    intro path
    simp [conjugate, List.map_map]
  have hconjugatePath : ∀ path start, sevenPath start path →
      sevenPath start.transpose (conjugate path) := by
    intro path
    induction path with
    | nil => intro start hpath; trivial
    | cons step tail ih =>
      obtain ⟨direction, next⟩ := step
      intro start hpath
      cases direction <;>
        simpa [conjugate, sevenPath, hedge] using And.intro hpath.1 (ih next hpath.2)
  have hconjugateTerminal : ∀ (path : List (Bool × SevenLabel)) (start : SevenLabel),
      (conjugate path).foldl (fun _ step => step.2) start.transpose =
        (path.foldl (fun _ step => step.2) start).transpose := by
    intro path
    induction path with
    | nil => intro start; rfl
    | cons step tail ih => intro start; simpa [conjugate] using ih step.2
  have hweights : ∀ path start column,
      (∀ row, sevenRowWeight start path row =
        sevenRowWeight start.transpose (conjugate path) row) ∧
      (∀ target, sevenColumnWeight start column path target =
        sevenColumnWeight start.transpose column (conjugate path) target) := by
    intro path
    induction path with
    | nil => intro start column; exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons step tail ih =>
      obtain ⟨direction, next⟩ := step
      intro start column
      obtain ⟨hrows, hcolumns⟩ := ih next (column + if direction then 1 else 0)
      constructor
      · intro row
        simp [conjugate, sevenRowWeight, hgrade, hrows, hshape]
      · intro target
        simp [conjugate, sevenColumnWeight, hgrade, hcolumns]
  have hslide : ∀ tail : List (Bool × SevenLabel),
      ∀ northwest northeast column axes cells,
      tail.Pairwise (fun first second => first.1 = false ∨ second.1 = true) →
      sevenSlide column northwest northeast tail = some (axes, cells) →
      cells.map (fun cell => (cell.1, cell.2.1)) =
        (List.range ((tail.map Prod.fst).count false)).reverse.map
          (fun row => (column + 1, row + 1)) := by
    intro tail
    induction tail with
    | nil =>
      intro northwest northeast column axes cells hsorted hcomputed
      simp only [sevenSlide, Option.some.injEq, Prod.mk.injEq] at hcomputed
      obtain ⟨rfl, rfl⟩ := hcomputed
      rfl
    | cons step tail ih =>
      obtain ⟨direction, next⟩ := step
      cases direction with
      | true =>
        intro northwest northeast column axes cells hsorted hcomputed
        simp only [sevenSlide, Option.some.injEq, Prod.mk.injEq] at hcomputed
        obtain ⟨rfl, rfl⟩ := hcomputed
        have hzero : (tail.map Prod.fst).count false = 0 := by
          apply List.count_eq_zero.mpr
          intro hmem
          obtain ⟨step, hstep, hequal⟩ := List.mem_map.mp hmem
          have := (List.pairwise_cons.mp hsorted).1 step hstep
          simp [hequal] at this
        simp [hzero]
      | false =>
        intro northwest northeast column axes cells hsorted hcomputed
        cases hinverse : sevenInverse northeast northwest next with
        | none => simp [sevenSlide, hinverse] at hcomputed
        | some output =>
          obtain ⟨southwest, entry⟩ := output
          cases hrecursive : sevenSlide column southwest next tail with
          | none => simp [sevenSlide, hinverse, hrecursive] at hcomputed
          | some output =>
            obtain ⟨remaining, points⟩ := output
            simp only [sevenSlide, hinverse, hrecursive, Option.bind_eq_bind,
              Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hcomputed
            obtain ⟨rfl, rfl⟩ := hcomputed
            have htail := ih southwest next column remaining points
              (List.pairwise_cons.mp hsorted).2 hrecursive
            simp [htail, List.range_succ, List.reverse_append]
  have htrace : ∀ path : List (Bool × SevenLabel), ∀ start column axes cells,
      sevenPath start path → sevenPeel start column path = some (axes, cells) →
      cells.map (fun cell => (cell.1, cell.2.1)) =
        sevenCells column (path.map Prod.fst) := by
    intro path
    induction path with
    | nil =>
      intro start column axes cells hpath hcomputed
      simp only [sevenPeel, Option.some.injEq, Prod.mk.injEq] at hcomputed
      obtain ⟨rfl, rfl⟩ := hcomputed
      rfl
    | cons step tail ih =>
      obtain ⟨direction, next⟩ := step
      cases direction with
      | false =>
        intro start column axes cells hpath hcomputed
        obtain ⟨middle, points, hmiddle, _, _, _, _, _⟩ :=
          seven_boundary_peeling next column tail hpath.2
        simp only [sevenPeel, hmiddle, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq, Prod.mk.injEq] at hcomputed
        obtain ⟨rfl, rfl⟩ := hcomputed
        exact ih next column middle points hpath.2 hmiddle
      | true =>
        intro start column axes cells hpath hcomputed
        obtain ⟨middle, points, hmiddle, _, hsorted, hperm, _, _⟩ :=
          seven_boundary_peeling next (column + 1) tail hpath.2
        cases hslid : sevenSlide column start next middle with
        | none => simp [sevenPeel, hmiddle, hslid] at hcomputed
        | some output =>
          obtain ⟨remaining, strip⟩ := output
          simp only [sevenPeel, hmiddle, hslid, Option.bind_eq_bind, Option.bind_some,
            Option.some.injEq, Prod.mk.injEq] at hcomputed
          obtain ⟨rfl, rfl⟩ := hcomputed
          have hpoints := ih next (column + 1) middle points hpath.2 hmiddle
          have hstrip := hslide middle start next column remaining strip hsorted hslid
          have hcount := hperm.count_eq false
          simp [sevenCells, List.map_append, hpoints, hstrip, hcount]
  have hzeroWeights : ∀ path : List (Bool × SevenLabel), ∀ column,
      (∀ step ∈ path, step.2 = .empty) →
      (∀ row, sevenRowWeight .empty path row = 0) ∧
      (∀ target, sevenColumnWeight .empty column path target = 0) := by
    intro path
    induction path with
    | nil => intro column hall; exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons step tail ih =>
      obtain ⟨direction, next⟩ := step
      intro column hall
      have hnext : next = .empty := hall (direction, next) (by simp)
      subst next
      obtain ⟨hrows, hcolumns⟩ := ih (column + if direction then 1 else 0)
        (fun step hstep => hall step (List.mem_cons_of_mem _ hstep))
      exact ⟨fun row => by simp [sevenRowWeight, hrows],
        fun target => by simp [sevenColumnWeight, hcolumns]⟩
  have hrightPath : sevenPath .empty (conjugate boundary) :=
    hconjugatePath boundary .empty hboundary
  have hrightTerminal :
      (conjugate boundary).foldl (fun _ step => step.2) .empty = .empty := by
    simpa [hterminal, SevenLabel.transpose] using hconjugateTerminal boundary .empty
  obtain ⟨leftAxes, left, hleft, _, hleftSorted, hleftPerm, _, hleftEmpty⟩ :=
    seven_boundary_peeling .empty column boundary hboundary
  obtain ⟨rightAxes, right, hright, _, hrightSorted, hrightPerm, _, hrightEmpty⟩ :=
    seven_boundary_peeling .empty column (conjugate boundary) hrightPath
  have hleftEmpty := hleftEmpty rfl hterminal
  have hrightEmpty := hrightEmpty rfl hrightTerminal
  have haxesShape : leftAxes.map Prod.fst = rightAxes.map Prod.fst := by
    apply List.Perm.eq_of_pairwise (le := fun first second : Bool =>
      first = false ∨ second = true)
    · intro first second hfirst hsecond hforward hbackward
      cases first <;> cases second <;> simp at hforward hbackward ⊢
    · simpa only [List.pairwise_map] using hleftSorted
    · simpa only [List.pairwise_map] using hrightSorted
    · have hrightPerm' : (rightAxes.map Prod.fst).Perm (boundary.map Prod.fst) := by
        simpa only [hshape] using hrightPerm
      exact hleftPerm.trans hrightPerm'.symm
  have hnormalize : ∀ axes : List (Bool × SevenLabel),
      (∀ step ∈ axes, step.2 = .empty) →
      axes = axes.map (fun step => (step.1, SevenLabel.empty)) := by
    intro axes hall
    conv_lhs => rw [← List.map_id axes]
    apply List.map_congr_left
    intro step hstep
    exact Prod.ext rfl (hall step hstep)
  have haxesEqual : leftAxes = rightAxes := by
    rw [hnormalize leftAxes hleftEmpty, hnormalize rightAxes hrightEmpty]
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun direction => (direction, SevenLabel.empty))) haxesShape
  subst rightAxes
  have hleftConservation :=
    seven_peeling_conservation .empty column boundary leftAxes left hboundary hleft
  have hrightConservation := seven_peeling_conservation .empty column
    (conjugate boundary) leftAxes right hrightPath hright
  have hzero := hzeroWeights leftAxes column hleftEmpty
  have hsameWeights := hweights boundary .empty column
  refine ⟨leftAxes, left, right, hleft, hright,
    htrace boundary .empty column leftAxes left hboundary hleft, ?_, ?_, ?_,
    hrightConservation.2.2.1, hrightConservation.2.2.2, hleftEmpty⟩
  · simpa only [hshape] using
      htrace (conjugate boundary) .empty column leftAxes right hrightPath hright
  · intro row
    have hleftRow := hleftConservation.1 row
    have hrightRow := hrightConservation.1 row
    have hweight := hsameWeights.1 row
    simp only [hzero.1 row, Nat.zero_add] at hleftRow hrightRow
    exact hleftRow.symm.trans (hweight.trans hrightRow)
  · intro target
    have hleftColumn := hleftConservation.2.1 target
    have hrightColumn := hrightConservation.2.1 target
    have hweight := hsameWeights.2 target
    simp only [hzero.2 target, Nat.zero_add] at hleftColumn hrightColumn
    exact hleftColumn.symm.trans (hweight.trans hrightColumn)

theorem seven_filling_permutation (n : ℕ) (cells : Finset (ℕ × ℕ))
    (hbounds : ∀ cell ∈ cells,
      1 ≤ cell.1 ∧ cell.1 ≤ n ∧ 1 ≤ cell.2 ∧ cell.2 ≤ n)
    (hcolumns : ∀ column, 1 ≤ column → column ≤ n →
      (cells.filter (fun cell => cell.1 = column)).card = 1)
    (hrows : ∀ row, 1 ≤ row → row ≤ n →
      (cells.filter (fun cell => cell.2 = row)).card = 1) :
    ∃! q : List ℕ, q.Perm (List.range' 1 n) ∧
      ∀ column row, 1 ≤ column → column ≤ n →
        ((column, row) ∈ cells ↔ q.getD (column - 1) 0 = row) := by
  classical
  have hcolumnUnique : ∀ column, 1 ≤ column → column ≤ n →
      ∃! cell, cell ∈ cells ∧ cell.1 = column := by
    intro column hpositive hbound
    simpa only [Finset.mem_filter] using
      Finset.card_eq_one_iff_existsUnique.mp (hcolumns column hpositive hbound)
  have hrowUnique : ∀ row, 1 ≤ row → row ≤ n →
      ∃! cell, cell ∈ cells ∧ cell.2 = row := by
    intro row hpositive hbound
    simpa only [Finset.mem_filter] using
      Finset.card_eq_one_iff_existsUnique.mp (hrows row hpositive hbound)
  let point := fun position : Fin n =>
    Classical.choose (hcolumnUnique (position.val + 1) (by omega) (by omega))
  have hpoint : ∀ position : Fin n,
      point position ∈ cells ∧ (point position).1 = position.val + 1 := by
    intro position
    exact (Classical.choose_spec
      (hcolumnUnique (position.val + 1) (by omega) (by omega))).1
  have hpointUnique : ∀ position : Fin n, ∀ cell ∈ cells,
      cell.1 = position.val + 1 → cell = point position := by
    intro position cell hcell hcolumn
    exact (Classical.choose_spec
      (hcolumnUnique (position.val + 1) (by omega) (by omega))).2 cell ⟨hcell, hcolumn⟩
  let value := fun position : Fin n => (point position).2
  have hvalueBounds : ∀ position : Fin n, 1 ≤ value position ∧ value position ≤ n := by
    intro position
    exact (hbounds (point position) (hpoint position).1).2.2
  have hinjective : Function.Injective value := by
    intro left right hequal
    obtain ⟨cell, hcell, hunique⟩ := hrowUnique (value left)
      (hvalueBounds left).1 (hvalueBounds left).2
    have hleft : point left = cell := hunique (point left) ⟨(hpoint left).1, rfl⟩
    have hright : point right = cell :=
      hunique (point right) ⟨(hpoint right).1, hequal.symm⟩
    have hcolumnsEqual := congrArg Prod.fst (hleft.trans hright.symm)
    rw [(hpoint left).2, (hpoint right).2] at hcolumnsEqual
    apply Fin.ext
    omega
  have hsurjective : ∀ row, 1 ≤ row → row ≤ n → ∃ position : Fin n,
      value position = row := by
    intro row hpositive hbound
    obtain ⟨cell, hcell, hunique⟩ := hrowUnique row hpositive hbound
    have hcellBounds := hbounds cell hcell.1
    let position : Fin n := ⟨cell.1 - 1, by omega⟩
    have hequal : cell = point position := hpointUnique position cell hcell.1 (by
      dsimp [position]
      omega)
    exact ⟨position, by simpa only [value, ← hequal] using hcell.2⟩
  let q := List.ofFn value
  have hnodup : q.Nodup := by
    apply List.pairwise_ofFn.mpr
    intro left right horder hequal
    exact (ne_of_lt horder) (hinjective hequal)
  have hperm : q.Perm (List.range' 1 n) := by
    apply (List.perm_ext_iff_of_nodup hnodup List.nodup_range').mpr
    intro row
    rw [List.mem_range'_1]
    change row ∈ List.ofFn value ↔ 1 ≤ row ∧ row < 1 + n
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨position, rfl⟩
      have := hvalueBounds position
      omega
    · rintro ⟨hpositive, hbound⟩
      exact hsurjective row hpositive (by omega)
  have hget : ∀ (position : ℕ) (hposition : position < n),
      q.getD position 0 = value ⟨position, hposition⟩ := by
    intro position hposition
    rw [List.getD_eq_getElem q 0 (by simpa [q] using hposition)]
    simp [q]
  have hgraph : ∀ column row, 1 ≤ column → column ≤ n →
      ((column, row) ∈ cells ↔ q.getD (column - 1) 0 = row) := by
    intro column row hpositive hbound
    rw [hget (column - 1) (by omega)]
    let position : Fin n := ⟨column - 1, by omega⟩
    change (column, row) ∈ cells ↔ value position = row
    constructor
    · intro hcell
      have hequal := hpointUnique position (column, row) hcell (by
        dsimp [position]
        omega)
      exact (congrArg Prod.snd hequal).symm
    · intro hequal
      have hcolumn : (point position).1 = column := by
        have := (hpoint position).2
        change (point position).1 = column - 1 + 1 at this
        omega
      have hpair : point position = (column, row) := Prod.ext hcolumn hequal
      simpa only [hpair] using (hpoint position).1
  refine ⟨q, ⟨hperm, hgraph⟩, ?_⟩
  intro other hother
  have hlength : other.length = q.length := hother.1.length_eq.trans hperm.length_eq.symm
  apply List.ext_getElem hlength
  intro position hotherPosition hqPosition
  have hn : position < n := by
    have := hother.1.length_eq
    simp only [List.length_range'] at this
    omega
  have hcell := (hother.2 (position + 1) (other.getD position 0) (by omega) (by omega)).mpr
    (by simp)
  have hequal := (hgraph (position + 1) (other.getD position 0) (by omega) (by omega)).mp hcell
  simpa only [Nat.add_sub_cancel, List.getD_eq_getElem other 0 hotherPosition,
    List.getD_eq_getElem q 0 hqPosition] using hequal.symm

end D5.S3.Combinatorics.MeshPattern.MeshPatternS21

/- GID: D5/S3/Combinatorics/MeshPattern/MeshPatternS21Switch
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/MeshPatternS21Switch
   mirror-E: none(waiver:restricted-filling-switch)
   anchors: [mathlib/module/Mathlib.Data.List.OfFn]
   utility: none
   digest: Conjugated restricted fillings extend uniquely while preserving corner statistics. -/
import D5.S3.Combinatorics.MeshPattern.MeshPatternS21Boundary
import Mathlib.Data.List.OfFn
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.MeshPattern.MeshPatternS21
theorem seven_active_switch (n : ℕ) (p : List ℕ) (hp : p.Perm (List.range' 1 n)) :
    (let labels := fun x y => (sevenDiagram p x y).getD .empty
    let directions := sevenOutline (activeRegion n p) n 0 n
    directions.count false = n ∧
    (sevenCells 0 directions).Nodup ∧
    (∀ cell, cell ∈ sevenCells 0 directions ↔ cell ∈ activeRegion n p) ∧
    sevenPath .empty (sevenBoundary labels 0 directions) ∧
    ∃ axes, sevenPeel .empty 0 (sevenBoundary labels 0 directions) =
      some (axes, (sevenCells 0 directions).map (fun cell =>
        (cell.1, cell.2, decide (p.getD (cell.1 - 1) 0 = cell.2)))) ∧
      (∀ step ∈ axes, step.2 = .empty)) ∧
    (let labels := fun x y => (sevenDiagram p x y).getD .empty
    let directions := sevenOutline (activeRegion n p) n 0 n
    let conjugate := (sevenBoundary labels 0 directions).map
      (fun step => (step.1, step.2.transpose))
    ∃ (q : List ℕ) (axes : List (Bool × SevenLabel)), q.Perm (List.range' 1 n) ∧
      sevenPeel .empty 0 conjugate = some (axes, (sevenCells 0 directions).map (fun cell =>
          (cell.1, cell.2, decide (q.getD (cell.1 - 1) 0 = cell.2)))) ∧
      (∀ step ∈ axes, step.2 = .empty) ∧
      (∀ x y, 1 ≤ x → x ≤ n → (x, y) ∉ activeRegion n p →
        (q.getD (x - 1) 0 = y ↔ p.getD (x - 1) 0 = y)) ∧
      (∀ maximum, 3 ≤ maximum → maximum ≤ n → (rectangle q (n - maximum + 3) maximum).card =
          (rectangle p (n - maximum + 3) maximum).card ∧
        ((∃ position ∈ rectangle q (n - maximum + 3) maximum, q.getD position 0 = maximum) ↔
          (∃ position ∈ rectangle p (n - maximum + 3) maximum, p.getD position 0 = maximum)) ∧
        (n - maximum + 2 ∈ rectangle q (n - maximum + 3) maximum ↔
          n - maximum + 2 ∈ rectangle p (n - maximum + 3) maximum)) ∧
      active n q = active n p ∧ activeRegion n q = activeRegion n p) := by
  classical
  let labels := fun x y => (sevenDiagram p x y).getD SevenLabel.empty
  let directions := sevenOutline (activeRegion n p) n 0 n
  obtain ⟨hheight, hnodup, hcoverage, hpathMain, hterminalMain, hlocal⟩ :=
    seven_active_outline n p hp
  have hstart : labels 0 n = .empty := by simp [labels, sevenDiagram]
  have seven_forward_peeling (labels : ℕ → ℕ → SevenLabel)
      (entries : ℕ → ℕ → Bool) (column : ℕ) (directions : List Bool)
      (hlocal : ∀ cell ∈ sevenCells column directions,
        sevenInverse (labels cell.1 cell.2) (labels (cell.1 - 1) cell.2)
          (labels cell.1 (cell.2 - 1)) =
            some (labels (cell.1 - 1) (cell.2 - 1), entries cell.1 cell.2)) :
      sevenPeel (labels column (directions.count false)) column
          (sevenBoundary labels column directions) =
        some (sevenBoundary labels column (List.replicate (directions.count false) false ++
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
    have hslide : ∀ height width column, (∀ row < height,
          sevenInverse (labels (column + 1) (row + 1)) (labels column (row + 1))
            (labels (column + 1) row) = some (labels column row, entries (column + 1) (row + 1))) →
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
          intro cell hcell; exact hlocal cell (by simp [sevenCells, hcell]))
        have hstrip := hslide (tail.count false) (tail.count true) column (by
          intro row hrow
          have hcell := hlocal (column + 1, row + 1) (by
            simp only [sevenCells, List.mem_append, List.mem_map, List.mem_reverse, List.mem_range]
            exact Or.inr ⟨row, hrow, rfl⟩)
          simpa using hcell)
        simp [sevenBoundary, sevenCells, sevenPeel, htail, hstrip,
          List.map_map, List.replicate_succ]
  have hconjugated (column : ℕ)
      (boundary : List (Bool × SevenLabel)) (hboundary : sevenPath .empty boundary)
      (hterminal : boundary.foldl (fun _ step => step.2) .empty = .empty) :
      let conjugate := boundary.map (fun step => (step.1, step.2.transpose))
      ∃ (axes : List (Bool × SevenLabel)) (left right : List (ℕ × ℕ × Bool)),
        sevenPeel .empty column boundary = some (axes, left) ∧
        sevenPeel .empty column conjugate = some (axes, right) ∧
        left.map (fun cell => (cell.1, cell.2.1)) = sevenCells column (boundary.map Prod.fst) ∧
        right.map (fun cell => (cell.1, cell.2.1)) = sevenCells column (boundary.map Prod.fst) ∧
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
      intro smaller larger; cases smaller <;> cases larger <;> rfl
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
        intro start hpath; cases direction <;>
          simpa [conjugate, sevenPath, hedge] using And.intro hpath.1 (ih next hpath.2)
    have hconjugateTerminal : ∀ (path : List (Bool × SevenLabel)) (start : SevenLabel),
        (conjugate path).foldl (fun _ step => step.2) start.transpose =
          (path.foldl (fun _ step => step.2) start).transpose := by
      intro path
      induction path with
      | nil => intro start; rfl
      | cons step tail ih => intro start; simpa [conjugate] using ih step.2
    have hweights : ∀ path start column, (∀ row, sevenRowWeight start path row =
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
    have hrightTerminal : (conjugate boundary).foldl (fun _ step => step.2) .empty = .empty := by
      simpa [hterminal, SevenLabel.transpose] using hconjugateTerminal boundary .empty
    obtain ⟨leftAxes, left, hleft, _, hleftSorted, hleftPerm, _, hleftEmpty, hleftCoordinates⟩ :=
      seven_boundary_peeling .empty column boundary hboundary
    obtain ⟨rightAxes, right, hright, _, hrightSorted, hrightPerm, _,
        hrightEmpty, hrightCoordinates⟩ :=
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
    have hnormalize : ∀ axes : List (Bool × SevenLabel), (∀ step ∈ axes, step.2 = .empty) →
        axes = axes.map (fun step => (step.1, SevenLabel.empty)) := by
      intro axes hall
      conv_lhs => rw [← List.map_id axes]
      apply List.map_congr_left
      intro step hstep; exact Prod.ext rfl (hall step hstep)
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
      hleftCoordinates, ?_, ?_, ?_,
      hrightConservation.2.2.1, hrightConservation.2.2.2, hleftEmpty⟩
    · simpa only [hshape] using
        hrightCoordinates
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
  have hcomputed := seven_forward_peeling labels
    (fun x y => decide (p.getD (x - 1) 0 = y)) 0 directions hlocal
  obtain ⟨axes, cells, hpeel, haxes, hsorted, hperm, hlast, hempty, _⟩ :=
    seven_boundary_peeling .empty 0 (sevenBoundary labels 0 directions) hpathMain
  have hequal : cells = (sevenCells 0 directions).map (fun cell =>
      (cell.1, cell.2, decide (p.getD (cell.1 - 1) 0 = cell.2))) := by
    rw [hheight, hstart, hpeel] at hcomputed
    exact congrArg Prod.snd (Option.some.inj hcomputed)
  have horiginal : sevenPeel .empty 0 (sevenBoundary labels 0 directions) =
      some (axes, (sevenCells 0 directions).map (fun cell =>
        (cell.1, cell.2, decide (p.getD (cell.1 - 1) 0 = cell.2)))) := by simpa [hequal] using hpeel
  have haxesEmptyOriginal := hempty rfl hterminalMain
  have hconjugated := hconjugated 0 (sevenBoundary labels 0 directions) hpathMain hterminalMain
  refine ⟨⟨hheight, hnodup, hcoverage, hpathMain, axes, horiginal, haxesEmptyOriginal⟩, ?_⟩
  let boundary := sevenBoundary labels 0 directions
  let coordinates := sevenCells 0 directions
  let original := coordinates.map (fun cell =>
    (cell.1, cell.2, decide (p.getD (cell.1 - 1) 0 = cell.2)))
  let originalAxes := axes
  have hempty := haxesEmptyOriginal
  obtain ⟨axes, left, right, hleft, hright, hleftCoordinates, hrightCoordinates,
      hrows, hcolumns, _, _, haxesEmpty⟩ :=
    hconjugated
  have hshape : boundary.map Prod.fst = directions := by
    have hall : ∀ (shape : List Bool) (column : ℕ),
        (sevenBoundary labels column shape).map Prod.fst = shape := by
      intro shape
      induction shape with
      | nil => intro column; rfl
      | cons direction tail ih =>
        intro column
        cases direction <;> simp [sevenBoundary, ih]
    exact hall directions 0
  have hleftEq : left = original := by
    rw [horiginal] at hleft
    exact congrArg Prod.snd (Option.some.inj hleft).symm
  have hrightShape : right.map (fun cell => (cell.1, cell.2.1)) = coordinates := by
    change right.map (fun cell => (cell.1, cell.2.1)) =
      sevenCells 0 (boundary.map Prod.fst) at hrightCoordinates
    simpa only [hshape] using hrightCoordinates
  rw [hleftEq] at hrows hcolumns
  let points := (Finset.range n).image (fun position =>
    (position + 1, p.getD position 0))
  let inside := ((right.filter (fun cell => cell.2.2)).map
    (fun cell => (cell.1, cell.2.1))).toFinset
  let outside := points.filter (fun cell => cell ∉ activeRegion n p)
  let combined := outside ∪ inside
  have hlength : p.length = n := by simpa using hp.length_eq
  have hvalues : ∀ position < n, 1 ≤ p.getD position 0 ∧ p.getD position 0 ≤ n := by
    intro position hposition
    have hmem := hp.mem_iff.mp (List.getElem_mem (show position < p.length by omega))
    rw [List.mem_range'_1] at hmem
    rw [List.getD_eq_getElem p 0 (by omega)]
    exact ⟨hmem.1, by omega⟩
  have hpoints : ∀ x y, (x, y) ∈ points ↔ 1 ≤ x ∧ x ≤ n ∧ p.getD (x - 1) 0 = y := by
    intro x y; simp only [points, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨position, hposition, rfl, rfl⟩
      exact ⟨by omega, by omega, by simp⟩
    · rintro ⟨hpositive, hbound, hvalue⟩
      exact ⟨x - 1, by omega, by omega, hvalue⟩
  have hregionBounds : ∀ cell ∈ activeRegion n p,
      1 ≤ cell.1 ∧ cell.1 ≤ n ∧ 1 ≤ cell.2 ∧ cell.2 ≤ n := by
    intro cell hcell
    obtain ⟨hpositive, hrow, maximum, hmaximum, hx, hy⟩ := hcell
    simp only [active, Finset.mem_filter, Finset.mem_range] at hmaximum
    omega
  have hinsideRegion : ∀ cell ∈ inside, cell ∈ activeRegion n p := by
    intro cell hcell
    obtain ⟨entry, ⟨hentry, _⟩, heq⟩ := by
      simpa only [inside, List.mem_toFinset, List.mem_map, List.mem_filter] using hcell
    have hcoordinate : (entry.1, entry.2.1) ∈ coordinates := by
      rw [← hrightShape]
      exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
    exact (hcoverage cell).mp (heq ▸ hcoordinate)
  have hcount : ∀ (trace : List (ℕ × ℕ × Bool))
      (hnodup : (trace.map (fun cell => (cell.1, cell.2.1))).Nodup)
      (predicate : ℕ × ℕ → Prop) [DecidablePred predicate],
      ((((trace.filter (fun cell => cell.2.2)).map
        (fun cell => (cell.1, cell.2.1))).toFinset).filter predicate).card =
        trace.countP (fun cell => decide (predicate (cell.1, cell.2.1)) && cell.2.2) := by
    intro trace hnodup predicate dp
    let selected := trace.filter (fun cell =>
      decide (predicate (cell.1, cell.2.1)) && cell.2.2)
    have hselected : (selected.map (fun cell => (cell.1, cell.2.1))).Nodup :=
      hnodup.sublist (List.filter_sublist.map _)
    have heq : (((trace.filter (fun cell => cell.2.2)).map
        (fun cell => (cell.1, cell.2.1))).toFinset).filter predicate =
        (selected.map (fun cell => (cell.1, cell.2.1))).toFinset := by
      ext cell
      simp only [Finset.mem_filter, List.mem_toFinset, List.mem_map,
        List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, selected]
      constructor
      · rintro ⟨⟨entry, ⟨hentry, hbit⟩, rfl⟩, hpredicate⟩
        exact ⟨entry, ⟨hentry, hpredicate, hbit⟩, rfl⟩
      · rintro ⟨entry, ⟨hentry, hpredicate, hbit⟩, rfl⟩
        exact ⟨⟨entry, ⟨hentry, hbit⟩, rfl⟩, hpredicate⟩
    rw [heq, List.toFinset_card_of_nodup hselected, List.length_map]
    exact (List.countP_eq_length_filter).symm
  have horiginalInside : (((original.filter (fun cell => cell.2.2)).map
      (fun cell => (cell.1, cell.2.1))).toFinset) =
        points.filter (fun cell => cell ∈ activeRegion n p) := by
    ext cell
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨entry, ⟨hentry, hbit⟩, rfl⟩
      obtain ⟨coordinate, hcoordinate, rfl⟩ := List.mem_map.mp hentry
      have hregion := (hcoverage coordinate).mp hcoordinate
      have hbounds := hregionBounds coordinate hregion
      exact ⟨(hpoints _ _).mpr ⟨hbounds.1, hbounds.2.1, of_decide_eq_true hbit⟩, hregion⟩
    · rintro ⟨hpoint, hregion⟩
      have hvalue := (hpoints _ _).mp hpoint
      exact ⟨(cell.1, cell.2, decide (p.getD (cell.1 - 1) 0 = cell.2)),
        ⟨List.mem_map.mpr ⟨cell, (hcoverage cell).mpr hregion, rfl⟩,
          decide_eq_true hvalue.2.2⟩, rfl⟩
  have hrightNodup : (right.map (fun cell => (cell.1, cell.2.1))).Nodup := hrightShape ▸ hnodup
  have horiginalNodup : (original.map (fun cell => (cell.1, cell.2.1))).Nodup := by
    simpa [original, List.map_map, Function.comp_def] using hnodup
  have hfibers : ∀ (predicate : ℕ × ℕ → Prop) [DecidablePred predicate],
      original.countP (fun cell => decide (predicate (cell.1, cell.2.1)) && cell.2.2) =
        right.countP (fun cell => decide (predicate (cell.1, cell.2.1)) && cell.2.2) →
      (inside.filter predicate).card =
        (points.filter (fun cell => cell ∈ activeRegion n p ∧ predicate cell)).card := by
    intro predicate dp hequal
    have heq : (points.filter (fun cell => cell ∈ activeRegion n p ∧ predicate cell)) =
        (points.filter (fun cell => cell ∈ activeRegion n p)).filter predicate := by
      ext cell
      simp [and_assoc]
    rw [heq, ← horiginalInside]
    rw [hcount right hrightNodup, hcount original horiginalNodup]
    exact hequal.symm
  have hinsideRows : ∀ row, (inside.filter (fun cell => cell.2 = row)).card =
      (points.filter (fun cell => cell ∈ activeRegion n p ∧ cell.2 = row)).card := by
    intro row
    apply hfibers (fun cell => cell.2 = row)
    simpa only [beq_eq_decide] using hrows row
  have hinsideColumns : ∀ column, (inside.filter (fun cell => cell.1 = column)).card =
      (points.filter (fun cell => cell ∈ activeRegion n p ∧ cell.1 = column)).card := by
    intro column
    apply hfibers (fun cell => cell.1 = column)
    simpa only [beq_eq_decide] using hcolumns column
  have hdisjoint : Disjoint outside inside := by
    apply Finset.disjoint_left.mpr
    intro cell hout hin; exact (Finset.mem_filter.mp hout).2 (hinsideRegion cell hin)
  have hcombinedBounds : ∀ cell ∈ combined, 1 ≤ cell.1 ∧ cell.1 ≤ n ∧ 1 ≤ cell.2 ∧ cell.2 ≤ n := by
    intro cell hcell
    rcases Finset.mem_union.mp hcell with hout | hin
    · have hpoint := (hpoints cell.1 cell.2).mp (Finset.mem_filter.mp hout).1
      have hvalue := hvalues (cell.1 - 1) (by omega)
      rw [hpoint.2.2] at hvalue
      exact ⟨hpoint.1, hpoint.2.1, hvalue⟩
    · exact hregionBounds cell (hinsideRegion cell hin)
  have hfullFibers : ∀ (predicate : ℕ × ℕ → Prop) [DecidablePred predicate],
      (inside.filter predicate).card =
        (points.filter (fun cell => cell ∈ activeRegion n p ∧ predicate cell)).card →
      (combined.filter predicate).card = (points.filter predicate).card := by
    intro predicate dp hequal
    have hout : outside.filter predicate =
        (points.filter predicate).filter (fun cell => cell ∉ activeRegion n p) := by
      ext cell; simp [outside, and_left_comm, and_comm]
    have hin : points.filter (fun cell => cell ∈ activeRegion n p ∧ predicate cell) =
        (points.filter predicate).filter (fun cell => cell ∈ activeRegion n p) := by
      ext cell; simp [and_left_comm, and_assoc, and_comm]
    change ((outside ∪ inside).filter predicate).card = _
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisjoint), hequal, hout, hin]
    have := Finset.card_filter_add_card_filter_not (s := points.filter predicate)
      (fun cell => cell ∈ activeRegion n p)
    omega
  have hpointsColumns : ∀ column, 1 ≤ column → column ≤ n →
      (points.filter (fun cell => cell.1 = column)).card = 1 := by
    intro column hpositive hbound
    have heq : points.filter (fun cell => cell.1 = column) = {(column, p.getD (column - 1) 0)} := by
      ext cell; simp only [Finset.mem_filter, Finset.mem_singleton]; constructor
      · rintro ⟨hcell, hcolumn⟩
        have hvalue := (hpoints cell.1 cell.2).mp hcell
        exact Prod.ext hcolumn (by simpa [hcolumn] using hvalue.2.2.symm)
      · rintro rfl; exact ⟨(hpoints _ _).mpr ⟨hpositive, hbound, rfl⟩, rfl⟩
    simp [heq]
  have hpointsRows : ∀ row, 1 ≤ row → row ≤ n →
      (points.filter (fun cell => cell.2 = row)).card = 1 := by
    intro row hpositive hbound
    have hmem : row ∈ p := hp.mem_iff.mpr (by simp [List.mem_range'_1]; omega)
    obtain ⟨position, hposition, hvalue⟩ := List.getElem_of_mem hmem
    have hpositionN : position < n := by omega
    have hget : p.getD position 0 = row := by
      rw [List.getD_eq_getElem p 0 hposition]; exact hvalue
    have heq : points.filter (fun cell => cell.2 = row) = {(position + 1, row)} := by
      ext cell; simp only [Finset.mem_filter, Finset.mem_singleton]; constructor
      · rintro ⟨hcell, hrow⟩
        have hpoint := (hpoints cell.1 cell.2).mp hcell
        have hequal : p.getD (cell.1 - 1) 0 = p.getD position 0 := by rw [hpoint.2.2, hget, hrow]
        rw [List.getD_eq_getElem p 0 (by omega), List.getD_eq_getElem p 0 hposition] at hequal
        have hinjective := (hp.nodup_iff.mpr List.nodup_range').getElem_inj_iff.mp hequal
        exact Prod.ext (by omega) hrow
      · rintro rfl; exact ⟨(hpoints _ _).mpr ⟨by omega, by omega, by simpa using hget⟩, rfl⟩
    simp [heq]
  have hfilling (n : ℕ) (cells : Finset (ℕ × ℕ)) (hbounds : ∀ cell ∈ cells,
        1 ≤ cell.1 ∧ cell.1 ≤ n ∧ 1 ≤ cell.2 ∧ cell.2 ≤ n)
      (hcolumns : ∀ column, 1 ≤ column → column ≤ n →
        (cells.filter (fun cell => cell.1 = column)).card = 1)
      (hrows : ∀ row, 1 ≤ row → row ≤ n → (cells.filter (fun cell => cell.2 = row)).card = 1) :
      ∃ q : List ℕ, q.Perm (List.range' 1 n) ∧ ∀ column row, 1 ≤ column → column ≤ n →
          ((column, row) ∈ cells ↔ q.getD (column - 1) 0 = row) := by
    classical
    have hcolumnUnique : ∀ column, 1 ≤ column → column ≤ n →
        ∃! cell, cell ∈ cells ∧ cell.1 = column := by
      intro column hpositive hbound; simpa only [Finset.mem_filter] using
        Finset.card_eq_one_iff_existsUnique.mp (hcolumns column hpositive hbound)
    have hrowUnique : ∀ row, 1 ≤ row → row ≤ n → ∃! cell, cell ∈ cells ∧ cell.2 = row := by
      intro row hpositive hbound; simpa only [Finset.mem_filter] using
        Finset.card_eq_one_iff_existsUnique.mp (hrows row hpositive hbound)
    let point := fun position : Fin n =>
      Classical.choose (hcolumnUnique (position.val + 1) (by omega) (by omega))
    have hpoint : ∀ position : Fin n,
        point position ∈ cells ∧ (point position).1 = position.val + 1 := by
      intro position
      exact (Classical.choose_spec (hcolumnUnique (position.val + 1) (by omega) (by omega))).1
    have hpointUnique : ∀ position : Fin n, ∀ cell ∈ cells,
        cell.1 = position.val + 1 → cell = point position := by
      intro position cell hcell hcolumn; exact (Classical.choose_spec
        (hcolumnUnique (position.val + 1) (by omega) (by omega))).2 cell ⟨hcell, hcolumn⟩
    let value := fun position : Fin n => (point position).2
    have hvalueBounds : ∀ position : Fin n, 1 ≤ value position ∧ value position ≤ n := by
      intro position; exact (hbounds (point position) (hpoint position).1).2.2
    have hinjective : Function.Injective value := by
      intro left right hequal
      obtain ⟨cell, hcell, hunique⟩ := hrowUnique (value left)
        (hvalueBounds left).1 (hvalueBounds left).2
      have hleft : point left = cell := hunique (point left) ⟨(hpoint left).1, rfl⟩
      have hright : point right = cell := hunique (point right) ⟨(hpoint right).1, hequal.symm⟩
      have hcolumnsEqual := congrArg Prod.fst (hleft.trans hright.symm)
      rw [(hpoint left).2, (hpoint right).2] at hcolumnsEqual; apply Fin.ext; omega
    have hsurjective : ∀ row, 1 ≤ row → row ≤ n → ∃ position : Fin n, value position = row := by
      intro row hpositive hbound
      obtain ⟨cell, hcell, hunique⟩ := hrowUnique row hpositive hbound
      have hcellBounds := hbounds cell hcell.1
      let position : Fin n := ⟨cell.1 - 1, by omega⟩
      have hequal : cell = point position := hpointUnique position cell hcell.1 (by
        dsimp [position]; omega)
      exact ⟨position, by simpa only [value, ← hequal] using hcell.2⟩
    let q := List.ofFn value
    have hnodup : q.Nodup := by
      apply List.pairwise_ofFn.mpr
      intro left right horder hequal; exact (ne_of_lt horder) (hinjective hequal)
    have hperm : q.Perm (List.range' 1 n) := by
      apply (List.perm_ext_iff_of_nodup hnodup List.nodup_range').mpr
      intro row; rw [List.mem_range'_1]; change row ∈ List.ofFn value ↔ 1 ≤ row ∧ row < 1 + n
      rw [List.mem_ofFn]; constructor
      · rintro ⟨position, rfl⟩
        have := hvalueBounds position; omega
      · rintro ⟨hpositive, hbound⟩; exact hsurjective row hpositive (by omega)
    have hget : ∀ (position : ℕ) (hposition : position < n),
        q.getD position 0 = value ⟨position, hposition⟩ := by
      intro position hposition; rw [List.getD_eq_getElem q 0 (by simpa [q] using hposition)]
      simp [q]
    have hgraph : ∀ column row, 1 ≤ column → column ≤ n →
        ((column, row) ∈ cells ↔ q.getD (column - 1) 0 = row) := by
      intro column row hpositive hbound; rw [hget (column - 1) (by omega)]
      let position : Fin n := ⟨column - 1, by omega⟩
      change (column, row) ∈ cells ↔ value position = row; constructor
      · intro hcell
        have hequal := hpointUnique position (column, row) hcell (by
          dsimp [position]; omega)
        exact (congrArg Prod.snd hequal).symm
      · intro hequal
        have hcolumn : (point position).1 = column := by
          have := (hpoint position).2; change (point position).1 = column - 1 + 1 at this; omega
        have hpair : point position = (column, row) := Prod.ext hcolumn hequal
        simpa only [hpair] using (hpoint position).1
    exact ⟨q, hperm, hgraph⟩
  obtain ⟨q, hq, hgraph⟩ := hfilling n combined hcombinedBounds
    (fun column hpositive hbound => (hfullFibers (fun cell => cell.1 = column)
      (hinsideColumns column)).trans
      (hpointsColumns column hpositive hbound))
    (fun row hpositive hbound => (hfullFibers (fun cell => cell.2 = row) (hinsideRows row)).trans
      (hpointsRows row hpositive hbound))
  have hinsideEqual : combined.filter (fun cell => cell ∈ activeRegion n p) = inside := by
    ext cell; simp only [Finset.mem_filter, combined, Finset.mem_union]; constructor
    · rintro ⟨hout | hin, hregion⟩
      · exact False.elim ((Finset.mem_filter.mp hout).2 hregion)
      · exact hin
    · intro hin; exact ⟨Or.inr hin, hinsideRegion cell hin⟩
  have houtsideEqual : combined.filter (fun cell => cell ∉ activeRegion n p) = outside := by
    ext cell; simp only [Finset.mem_filter, combined, Finset.mem_union]; constructor
    · rintro ⟨hout | hin, hregion⟩
      · exact hout
      · exact False.elim (hregion (hinsideRegion cell hin))
    · intro hout; exact ⟨Or.inl hout, (Finset.mem_filter.mp hout).2⟩
  have hconservation : ∀ (region : Set (ℕ × ℕ))
    (hregion : region ⊆ ferrersRegion n) (left right : Finset (ℕ × ℕ))
    (houtside : left.filter (fun cell => cell ∉ region) = right.filter (fun cell => cell ∉ region))
    (hrows : ∀ y, (left.filter (fun cell => cell ∈ region ∧ cell.2 = y)).card =
        (right.filter (fun cell => cell ∈ region ∧ cell.2 = y)).card)
    (hcolumns : ∀ x, (left.filter (fun cell => cell ∈ region ∧ cell.1 = x)).card =
        (right.filter (fun cell => cell ∈ region ∧ cell.1 = x)).card),
    ∀ maximum, 3 ≤ maximum → maximum ≤ n →
      (left.filter (fun cell => cell.1 ≤ n - maximum + 3 ∧ cell.2 ≤ maximum)).card =
        (right.filter (fun cell => cell.1 ≤ n - maximum + 3 ∧ cell.2 ≤ maximum)).card ∧
      (left.filter (fun cell => cell.2 = maximum ∧ cell.1 ≤ n - maximum + 3)).card =
        (right.filter (fun cell => cell.2 = maximum ∧ cell.1 ≤ n - maximum + 3)).card ∧
      (left.filter (fun cell => cell.1 = n - maximum + 3 ∧ cell.2 ≤ maximum)).card =
        (right.filter (fun cell => cell.1 = n - maximum + 3 ∧ cell.2 ≤ maximum)).card := by
    intro region hregion left right houtside hrows hcolumns
    let leftInside := left.filter (fun cell => cell ∈ region)
    let rightInside := right.filter (fun cell => cell ∈ region)
    have hbounds : ∀ cell ∈ region, cell.1 ≤ n ∧ cell.2 ≤ n ∧ cell.1 + cell.2 ≤ n + 3 := by
      intro cell hcell
      obtain ⟨maximum, hthree, hbound, _, hx, _, hy⟩ := hregion hcell
      exact ⟨by omega, by omega, by omega⟩
    have hcoordinateCounts : ∀ projection : (ℕ × ℕ) → ℕ, (∀ cell ∈ region, projection cell ≤ n) →
        (∀ index, (leftInside.filter (fun cell => projection cell = index)).card =
          (rightInside.filter (fun cell => projection cell = index)).card) →
        ∀ (test : ℕ → Prop) [DecidablePred test],
          (leftInside.filter (fun cell => test (projection cell))).card =
            (rightInside.filter (fun cell => test (projection cell))).card := by
      intro projection hprojection hfibers test testDec
      let indices := (Finset.range (n + 1)).filter test
      have hleft : leftInside.filter (fun cell => projection cell ∈ indices) =
          leftInside.filter (fun cell => test (projection cell)) := by
        ext cell; simp only [indices, Finset.mem_filter, Finset.mem_range]; constructor
        · rintro ⟨hcell, _, htest⟩; exact ⟨hcell, htest⟩
        · rintro ⟨hcell, htest⟩
          have hbound := hprojection cell (Finset.mem_filter.mp hcell).2
          exact ⟨hcell, by omega, htest⟩
      have hright : rightInside.filter (fun cell => projection cell ∈ indices) =
          rightInside.filter (fun cell => test (projection cell)) := by
        ext cell; simp only [indices, Finset.mem_filter, Finset.mem_range]; constructor
        · rintro ⟨hcell, _, htest⟩; exact ⟨hcell, htest⟩
        · rintro ⟨hcell, htest⟩
          have hbound := hprojection cell (Finset.mem_filter.mp hcell).2
          exact ⟨hcell, by omega, htest⟩
      calc
        _ = ∑ index ∈ indices,
            (leftInside.filter (fun cell => projection cell = index)).card := by
          rw [Finset.sum_card_fiberwise_eq_card_filter, hleft]
        _ = ∑ index ∈ indices, (rightInside.filter (fun cell => projection cell = index)).card :=
          Finset.sum_congr rfl (fun index _ => hfibers index)
        _ = _ := by rw [Finset.sum_card_fiberwise_eq_card_filter, hright]
    have hrowCounts : ∀ (test : ℕ → Prop) [DecidablePred test],
        (leftInside.filter (fun cell => test cell.2)).card =
          (rightInside.filter (fun cell => test cell.2)).card := by
      apply hcoordinateCounts Prod.snd
      · exact fun cell hcell => (hbounds cell hcell).2.1
      · intro index; simpa only [leftInside, rightInside, Finset.filter_filter] using hrows index
    have hcolumnCounts : ∀ (test : ℕ → Prop) [DecidablePred test],
        (leftInside.filter (fun cell => test cell.1)).card =
          (rightInside.filter (fun cell => test cell.1)).card := by
      apply hcoordinateCounts Prod.fst
      · exact fun cell hcell => (hbounds cell hcell).1
      · intro index; simpa only [leftInside, rightInside, Finset.filter_filter] using hcolumns index
    have htotal : leftInside.card = rightInside.card := by simpa using hrowCounts (fun _ => True)
    have hsplit : ∀ (filling : Finset (ℕ × ℕ)) (test : (ℕ × ℕ) → Prop) [DecidablePred test],
        (filling.filter test).card =
          ((filling.filter (fun cell => cell ∈ region)).filter test).card +
          ((filling.filter (fun cell => cell ∉ region)).filter test).card := by
      intro filling test testDec
      have hcard := Finset.card_filter_add_card_filter_not
        (s := filling.filter test) (fun cell => cell ∈ region)
      simpa only [Finset.filter_filter, and_comm] using hcard.symm
    intro maximum hthree hbound
    let width := n - maximum + 3
    have hnoNE : ∀ cell ∈ region, width < cell.1 → cell.2 ≤ maximum := by
      intro cell hcell hx
      have := hbounds cell hcell; dsimp [width] at *; omega
    have hdecomposition : ∀ inside : Finset (ℕ × ℕ), (∀ cell ∈ inside, cell ∈ region) →
        (inside.filter (fun cell => cell.1 ≤ width ∧ cell.2 ≤ maximum)).card +
          (inside.filter (fun cell => maximum < cell.2)).card +
          (inside.filter (fun cell => width < cell.1)).card = inside.card := by
      intro inside hins
      have hvertical := Finset.card_filter_add_card_filter_not
        (s := inside) (fun cell => cell.2 ≤ maximum)
      have hhorizontal := Finset.card_filter_add_card_filter_not
        (s := inside.filter (fun cell => cell.2 ≤ maximum)) (fun cell => cell.1 ≤ width)
      have hrightStrip : inside.filter (fun cell => cell.2 ≤ maximum ∧ width < cell.1) =
          inside.filter (fun cell => width < cell.1) := by
        ext cell; simp only [Finset.mem_filter]; constructor
        · rintro ⟨hcell, _, hx⟩; exact ⟨hcell, hx⟩
        · rintro ⟨hcell, hx⟩; exact ⟨hcell, hnoNE cell (hins cell hcell) hx, hx⟩
      simp only [Nat.not_le] at hvertical
      simp only [Finset.filter_filter, Nat.not_le] at hhorizontal
      rw [hrightStrip] at hhorizontal
      have hrect : inside.filter (fun cell => cell.2 ≤ maximum ∧ cell.1 ≤ width) =
          inside.filter (fun cell => cell.1 ≤ width ∧ cell.2 ≤ maximum) := by simp only [and_comm]
      rw [hrect] at hhorizontal; omega
    have hrectCounts : (leftInside.filter (fun cell => cell.1 ≤ width ∧ cell.2 ≤ maximum)).card =
          (rightInside.filter (fun cell => cell.1 ≤ width ∧ cell.2 ≤ maximum)).card := by
      have hleft := hdecomposition leftInside (fun _ hcell => (Finset.mem_filter.mp hcell).2)
      have hright := hdecomposition rightInside (fun _ hcell => (Finset.mem_filter.mp hcell).2)
      have hrowsAbove := hrowCounts (fun y => maximum < y)
      have hcolumnsRight := hcolumnCounts (fun x => width < x); omega
    have hrowCorner : ∀ filling : Finset (ℕ × ℕ),
        (filling.filter (fun cell => cell ∈ region ∧ cell.2 = maximum ∧ cell.1 ≤ width)) =
          filling.filter (fun cell => cell ∈ region ∧ cell.2 = maximum) := by
      intro filling; ext cell; simp only [Finset.mem_filter]; constructor
      · rintro ⟨hcell, hregionCell, hy, _⟩; exact ⟨hcell, hregionCell, hy⟩
      · rintro ⟨hcell, hregionCell, hy⟩
        have := hbounds cell hregionCell; refine ⟨hcell, hregionCell, hy, ?_⟩; dsimp [width]; omega
    have hcolumnCorner : ∀ filling : Finset (ℕ × ℕ),
        (filling.filter (fun cell => cell ∈ region ∧ cell.1 = width ∧ cell.2 ≤ maximum)) =
          filling.filter (fun cell => cell ∈ region ∧ cell.1 = width) := by
      intro filling; ext cell; simp only [Finset.mem_filter]; constructor
      · rintro ⟨hcell, hregionCell, hx, _⟩; exact ⟨hcell, hregionCell, hx⟩
      · rintro ⟨hcell, hregionCell, hx⟩
        have := hbounds cell hregionCell; refine ⟨hcell, hregionCell, hx, ?_⟩
        dsimp [width] at hx; omega
    simp only [width] at hrowCorner hcolumnCorner
    refine ⟨?_, ?_, ?_⟩
    · rw [hsplit left (fun cell => cell.1 ≤ n - maximum + 3 ∧ cell.2 ≤ maximum),
        hsplit right (fun cell => cell.1 ≤ n - maximum + 3 ∧ cell.2 ≤ maximum), houtside]
      exact congrArg (fun count => count + ((right.filter (fun cell => cell ∉ region)).filter
          (fun cell => cell.1 ≤ width ∧ cell.2 ≤ maximum)).card) hrectCounts
    · rw [hsplit left (fun cell => cell.2 = maximum ∧ cell.1 ≤ n - maximum + 3),
        hsplit right (fun cell => cell.2 = maximum ∧ cell.1 ≤ n - maximum + 3), houtside]
      simp only [Finset.filter_filter, hrowCorner]
      simpa only [Finset.filter_filter] using congrArg (fun count => count +
        ((right.filter (fun cell => cell ∉ region)).filter
          (fun cell => cell.2 = maximum ∧ cell.1 ≤ width)).card) (hrows maximum)
    · rw [hsplit left (fun cell => cell.1 = n - maximum + 3 ∧ cell.2 ≤ maximum),
        hsplit right (fun cell => cell.1 = n - maximum + 3 ∧ cell.2 ≤ maximum), houtside]
      simp only [Finset.filter_filter, hcolumnCorner]
      simpa only [Finset.filter_filter] using congrArg (fun count => count +
        ((right.filter (fun cell => cell ∉ region)).filter
          (fun cell => cell.1 = width ∧ cell.2 ≤ maximum)).card) (hcolumns width)
  have hactive : ∀ maximum, maximum ∈ active n p ↔ 3 ≤ maximum ∧ maximum ≤ n ∧
      (rectangle p (n - maximum + 3) maximum).card = 3 := by
    intro maximum; simp only [active, Finset.mem_filter, Finset.mem_range]; omega
  have hsub : activeRegion n p ⊆ ferrersRegion n := by
    rintro ⟨x, y⟩ ⟨hx, hy, maximum, hmaximum, hxbound, hybound⟩
    have hbound := (hactive maximum).mp hmaximum
    exact ⟨maximum, hbound.1, hbound.2.1, hx, hxbound, hy, hybound⟩
  have hpreserve := hconservation (activeRegion n p) hsub points combined houtsideEqual.symm
    (fun row => by
      have heq : combined.filter (fun cell => cell ∈ activeRegion n p ∧ cell.2 = row) =
          inside.filter (fun cell => cell.2 = row) := by rw [← hinsideEqual, Finset.filter_filter]
      rw [heq]; exact (hinsideRows row).symm)
    (fun column => by
      have heq : combined.filter (fun cell => cell ∈ activeRegion n p ∧ cell.1 = column) =
          inside.filter (fun cell => cell.1 = column) := by
        rw [← hinsideEqual, Finset.filter_filter]
      rw [heq]; exact (hinsideColumns column).symm)
  have hrectangle : ∀ (permutation : List ℕ) (filling : Finset (ℕ × ℕ)),
      (∀ cell ∈ filling, 1 ≤ cell.1 ∧ cell.1 ≤ n) →
      (∀ column row, 1 ≤ column → column ≤ n →
        ((column, row) ∈ filling ↔ permutation.getD (column - 1) 0 = row)) →
      ∀ width height, width ≤ n →
      (rectangle permutation width height).card =
        (filling.filter (fun cell => cell.1 ≤ width ∧ cell.2 ≤ height)).card := by
    intro permutation filling hbounds hget width height hwidth
    apply Finset.card_bij (fun position _ => (position + 1, permutation.getD position 0))
    · intro position hposition
      have hpos : position < width ∧ permutation.getD position 0 ≤ height := by
        simpa [rectangle] using hposition
      exact Finset.mem_filter.mpr ⟨(hget _ _ (by omega) (by omega)).mpr (by simp), by omega, hpos.2⟩
    · intro first hfirst second hsecond hequal
      have := congrArg Prod.fst hequal; omega
    · intro cell hcell
      obtain ⟨hcell, hwidthCell, hheightCell⟩ := Finset.mem_filter.mp hcell
      have hbound := hbounds cell hcell
      have hvalue := (hget _ _ hbound.1 hbound.2).mp hcell; refine ⟨cell.1 - 1, ?_, ?_⟩
      · simp only [rectangle, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hvalue.trans_le hheightCell⟩
      · exact Prod.ext (by omega) hvalue
  have hpointsBounds : ∀ cell ∈ points, 1 ≤ cell.1 ∧ cell.1 ≤ n := by
    intro cell hcell; exact ⟨((hpoints _ _).mp hcell).1, ((hpoints _ _).mp hcell).2.1⟩
  have hpointGraph : ∀ column row, 1 ≤ column → column ≤ n →
      ((column, row) ∈ points ↔ p.getD (column - 1) 0 = row) := by
    intro column row hpositive hbound; simp only [hpoints, hpositive, hbound, true_and]
  have hcounts : ∀ maximum, 3 ≤ maximum → maximum ≤ n →
      (rectangle p (n - maximum + 3) maximum).card =
        (rectangle q (n - maximum + 3) maximum).card := by
    intro maximum hthree hbound; rw [hrectangle p points hpointsBounds hpointGraph _ _ (by omega),
      hrectangle q combined (fun cell hcell =>
        ⟨(hcombinedBounds cell hcell).1, (hcombinedBounds cell hcell).2.1⟩)
        hgraph _ _ (by omega)]
    exact (hpreserve maximum hthree hbound).1
  have hregionEqual : active n p = active n q ∧ activeRegion n p = activeRegion n q := by
    have heq : active n p = active n q := by
      ext maximum; simp only [active, Finset.mem_filter, Finset.mem_range]; constructor
      · rintro ⟨hbound, hthree, hcard⟩
        exact ⟨hbound, hthree, (hcounts maximum hthree (by omega)).symm.trans hcard⟩
      · rintro ⟨hbound, hthree, hcard⟩
        exact ⟨hbound, hthree, (hcounts maximum hthree (by omega)).trans hcard⟩
    exact ⟨heq, by simp only [activeRegion, heq]⟩
  have hentry : ∀ entry ∈ right, entry.2.2 = decide (q.getD (entry.1 - 1) 0 = entry.2.1) := by
    intro entry hentry
    have hcoordinate : (entry.1, entry.2.1) ∈ coordinates := by
      rw [← hrightShape]; exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
    have hregion := (hcoverage _).mp hcoordinate
    have hbound := hregionBounds _ hregion; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]
    rw [← hgraph _ _ hbound.1 hbound.2.1]; constructor
    · intro hbit; exact Finset.mem_union.mpr (Or.inr (by
        simp only [inside, List.mem_toFinset, List.mem_map, List.mem_filter]
        exact ⟨entry, ⟨hentry, hbit⟩, rfl⟩))
    · intro hcombined
      have hin : (entry.1, entry.2.1) ∈ inside := by
        rw [← hinsideEqual]; exact Finset.mem_filter.mpr ⟨hcombined, hregion⟩
      obtain ⟨other, ⟨hother, hbit⟩, hequal⟩ := by
        simpa only [inside, List.mem_toFinset, List.mem_map, List.mem_filter] using hin
      have heq : other = entry := List.inj_on_of_nodup_map hrightNodup hother hentry hequal
      simpa [heq] using hbit
  have htraceEqual : right = coordinates.map (fun cell =>
      (cell.1, cell.2, decide (q.getD (cell.1 - 1) 0 = cell.2))) := by
    rw [← hrightShape, List.map_map]
    conv_lhs => rw [← List.map_id right]
    apply List.map_congr_left
    intro entry hmem; exact Prod.ext rfl (Prod.ext rfl (hentry entry hmem))
  refine ⟨q, axes, hq, ?_, haxesEmpty, ?_, ?_, hregionEqual.1.symm, hregionEqual.2.symm⟩
  · simpa only [htraceEqual] using hright
  · intro x y hpositive hbound hnot
    rw [← hgraph x y hpositive hbound, ← hpointGraph x y hpositive hbound]
    have := congrArg (fun filling => (x, y) ∈ filling) houtsideEqual
    exact by simpa only [Finset.mem_filter, hnot, and_true, not_false_eq_true, outside] using
      (Iff.of_eq this)
  · intro maximum hthree hbound
    have hnonempty : ∀ (permutation : List ℕ) (filling : Finset (ℕ × ℕ)),
        (∀ cell ∈ filling, 1 ≤ cell.1 ∧ cell.1 ≤ n) →
        (∀ column row, 1 ≤ column → column ≤ n →
          ((column, row) ∈ filling ↔ permutation.getD (column - 1) 0 = row)) →
        ((filling.filter (fun cell => cell.2 = maximum ∧ cell.1 ≤ n - maximum + 3)).Nonempty ↔
          ∃ position ∈ rectangle permutation (n - maximum + 3) maximum,
            permutation.getD position 0 = maximum) := by
      intro permutation filling hbounds hget; constructor
      · rintro ⟨cell, hcell⟩
        obtain ⟨hcell, hrow, hwidth⟩ := Finset.mem_filter.mp hcell
        have hbounds := hbounds cell hcell
        have hvalue := (hget _ _ hbounds.1 hbounds.2).mp hcell
        refine ⟨cell.1 - 1, ?_, hvalue.trans hrow⟩
        simp only [rectangle, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by rw [hvalue, hrow]⟩
      · rintro ⟨position, hposition, hvalue⟩
        have hpos : position < n - maximum + 3 :=
          Finset.mem_range.mp (Finset.mem_filter.mp hposition).1
        refine ⟨(position + 1, maximum), Finset.mem_filter.mpr ⟨?_, rfl, by omega⟩⟩
        exact (hget _ _ (by omega) (by omega)).mpr (by simpa using hvalue)
    have hcolumnNonempty : ∀ (permutation : List ℕ) (filling : Finset (ℕ × ℕ)),
        (∀ column row, 1 ≤ column → column ≤ n →
          ((column, row) ∈ filling ↔ permutation.getD (column - 1) 0 = row)) →
        ((filling.filter (fun cell => cell.1 = n - maximum + 3 ∧ cell.2 ≤ maximum)).Nonempty ↔
          n - maximum + 2 ∈ rectangle permutation (n - maximum + 3) maximum) := by
      intro permutation filling hget; constructor
      · rintro ⟨cell, hcell⟩
        obtain ⟨hcell, hcolumn, hrow⟩ := Finset.mem_filter.mp hcell
        have hvalue := (hget cell.1 cell.2 (by omega) (by omega)).mp hcell
        simp only [rectangle, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by simpa [hcolumn] using hvalue.trans_le hrow⟩
      · intro hposition
        have hvalue := (Finset.mem_filter.mp hposition).2
        exact ⟨(n - maximum + 3, permutation.getD (n - maximum + 2) 0),
          Finset.mem_filter.mpr ⟨(hget _ _ (by omega) (by omega)).mpr (by simp),
            rfl, hvalue⟩⟩
    refine ⟨(hcounts maximum hthree hbound).symm, ?_, ?_⟩
    · rw [← hnonempty q combined (fun cell hcell =>
        ⟨(hcombinedBounds cell hcell).1, (hcombinedBounds cell hcell).2.1⟩) hgraph,
        ← hnonempty p points hpointsBounds hpointGraph, ← Finset.card_pos,
        ← Finset.card_pos, (hpreserve maximum hthree hbound).2.1]
    · rw [← hcolumnNonempty q combined hgraph,
        ← hcolumnNonempty p points hpointGraph, ← Finset.card_pos,
        ← Finset.card_pos, (hpreserve maximum hthree hbound).2.2]

end D5.S3.Combinatorics.MeshPattern.MeshPatternS21

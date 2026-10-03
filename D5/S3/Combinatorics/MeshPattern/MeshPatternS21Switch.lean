/- GID: D5/S3/Combinatorics/MeshPattern/MeshPatternS21Switch
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/MeshPatternS21Switch
   mirror-E: none(waiver:restricted-filling-switch)
   anchors: []
   utility: none
   digest: Conjugated restricted fillings extend uniquely while preserving corner statistics. -/

import D5.S3.Combinatorics.MeshPattern.MeshPatternS21Boundary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MeshPattern.MeshPatternS21

theorem seven_switch_realization (n : ℕ) (p : List ℕ)
    (hp : p.Perm (List.range' 1 n)) :
    let labels := fun x y => (sevenDiagram p x y).getD .empty
    let directions := sevenOutline (activeRegion n p) n 0 n
    let conjugate := (sevenBoundary labels 0 directions).map
      (fun step => (step.1, step.2.transpose))
    ∃ (q : List ℕ) (axes : List (Bool × SevenLabel)),
      q.Perm (List.range' 1 n) ∧
      sevenPeel .empty 0 conjugate = some (axes,
        (sevenCells 0 directions).map (fun cell =>
          (cell.1, cell.2, decide (q.getD (cell.1 - 1) 0 = cell.2)))) ∧
      (∀ step ∈ axes, step.2 = .empty) ∧
      (∀ x y, 1 ≤ x → x ≤ n → (x, y) ∉ activeRegion n p →
        (q.getD (x - 1) 0 = y ↔ p.getD (x - 1) 0 = y)) ∧
      (∀ maximum, 3 ≤ maximum → maximum ≤ n →
        (rectangle q (n - maximum + 3) maximum).card =
          (rectangle p (n - maximum + 3) maximum).card ∧
        ((∃ position ∈ rectangle q (n - maximum + 3) maximum,
          q.getD position 0 = maximum) ↔
          (∃ position ∈ rectangle p (n - maximum + 3) maximum,
            p.getD position 0 = maximum)) ∧
        (n - maximum + 2 ∈ rectangle q (n - maximum + 3) maximum ↔
          n - maximum + 2 ∈ rectangle p (n - maximum + 3) maximum)) ∧
      active n q = active n p ∧ activeRegion n q = activeRegion n p := by
  classical
  let labels := fun x y => (sevenDiagram p x y).getD SevenLabel.empty
  let directions := sevenOutline (activeRegion n p) n 0 n
  let boundary := sevenBoundary labels 0 directions
  let coordinates := sevenCells 0 directions
  let original := coordinates.map (fun cell =>
    (cell.1, cell.2, decide (p.getD (cell.1 - 1) 0 = cell.2)))
  obtain ⟨hheight, hnodup, hcoverage, hpath, originalAxes, horiginal, hempty⟩ :=
    seven_active_boundary n p hp
  have hterminal : boundary.foldl (fun _ step => step.2) .empty = .empty := by
    have hfold : ∀ (shape : List Bool) (column : ℕ),
        (sevenBoundary labels column shape).foldl (fun _ step => step.2)
          (labels column (shape.count false)) =
            labels (column + shape.count true) 0 := by
      intro shape
      induction shape with
      | nil => intro column; simp [sevenBoundary]
      | cons direction tail ih =>
        intro column
        cases direction with
        | false => simpa [sevenBoundary] using ih column
        | true =>
          simpa [sevenBoundary, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ih (column + 1)
    have hstart : labels 0 (directions.count false) = .empty := by
      simp [labels, sevenDiagram]
    have hzero : ∀ column, labels column 0 = .empty := by
      intro column
      cases column <;> simp [labels, sevenDiagram]
    simpa [boundary, hstart, hzero] using hfold directions 0
  obtain ⟨axes, left, right, hleft, hright, hleftCoordinates, hrightCoordinates,
      hrows, hcolumns, _, _, haxesEmpty⟩ :=
    seven_conjugated_reconstruction 0 boundary hpath hterminal
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
  have hpoints : ∀ x y, (x, y) ∈ points ↔
      1 ≤ x ∧ x ≤ n ∧ p.getD (x - 1) 0 = y := by
    intro x y
    simp only [points, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨position, hposition, rfl, rfl⟩
      exact ⟨by omega, by omega, by simp⟩
    · rintro ⟨hpositive, hbound, hvalue⟩
      exact ⟨x - 1, by omega, by omega, hvalue⟩
  have hregionBounds : ∀ cell ∈ activeRegion n p,
      1 ≤ cell.1 ∧ cell.1 ≤ n ∧ 1 ≤ cell.2 ∧ cell.2 ≤ n := by
    intro cell hcell
    obtain ⟨maximum, hthree, hmaximum, _, hx, _, hy⟩ :=
      (active_geometry n p hp).1 hcell
    obtain ⟨hpositive, hrow, _⟩ := hcell
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
      exact ⟨(hpoints _ _).mpr ⟨hbounds.1, hbounds.2.1,
        of_decide_eq_true hbit⟩, hregion⟩
    · rintro ⟨hpoint, hregion⟩
      have hvalue := (hpoints _ _).mp hpoint
      exact ⟨(cell.1, cell.2, decide (p.getD (cell.1 - 1) 0 = cell.2)),
        ⟨List.mem_map.mpr ⟨cell, (hcoverage cell).mpr hregion, rfl⟩,
          decide_eq_true hvalue.2.2⟩, rfl⟩
  have hrightNodup : (right.map (fun cell => (cell.1, cell.2.1))).Nodup :=
    hrightShape ▸ hnodup
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
    intro cell hout hin
    exact (Finset.mem_filter.mp hout).2 (hinsideRegion cell hin)
  have hcombinedBounds : ∀ cell ∈ combined,
      1 ≤ cell.1 ∧ cell.1 ≤ n ∧ 1 ≤ cell.2 ∧ cell.2 ≤ n := by
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
      ext cell
      simp [outside, and_left_comm, and_comm]
    have hin : points.filter (fun cell => cell ∈ activeRegion n p ∧ predicate cell) =
        (points.filter predicate).filter (fun cell => cell ∈ activeRegion n p) := by
      ext cell
      simp [and_left_comm, and_assoc, and_comm]
    change ((outside ∪ inside).filter predicate).card = _
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisjoint), hequal, hout, hin]
    have := Finset.card_filter_add_card_filter_not (s := points.filter predicate)
      (fun cell => cell ∈ activeRegion n p)
    omega
  have hpointsColumns : ∀ column, 1 ≤ column → column ≤ n →
      (points.filter (fun cell => cell.1 = column)).card = 1 := by
    intro column hpositive hbound
    have heq : points.filter (fun cell => cell.1 = column) =
        {(column, p.getD (column - 1) 0)} := by
      ext cell
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hcell, hcolumn⟩
        have hvalue := (hpoints cell.1 cell.2).mp hcell
        exact Prod.ext hcolumn (by simpa [hcolumn] using hvalue.2.2.symm)
      · rintro rfl
        exact ⟨(hpoints _ _).mpr ⟨hpositive, hbound, rfl⟩, rfl⟩
    simp [heq]
  have hpointsRows : ∀ row, 1 ≤ row → row ≤ n →
      (points.filter (fun cell => cell.2 = row)).card = 1 := by
    intro row hpositive hbound
    have hmem : row ∈ p := hp.mem_iff.mpr (by simp [List.mem_range'_1]; omega)
    obtain ⟨position, hposition, hvalue⟩ := List.getElem_of_mem hmem
    have hpositionN : position < n := by omega
    have hget : p.getD position 0 = row := by
      rw [List.getD_eq_getElem p 0 hposition]
      exact hvalue
    have heq : points.filter (fun cell => cell.2 = row) = {(position + 1, row)} := by
      ext cell
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hcell, hrow⟩
        have hpoint := (hpoints cell.1 cell.2).mp hcell
        have hequal : p.getD (cell.1 - 1) 0 = p.getD position 0 := by
          rw [hpoint.2.2, hget, hrow]
        rw [List.getD_eq_getElem p 0 (by omega),
          List.getD_eq_getElem p 0 hposition] at hequal
        have hinjective := (hp.nodup_iff.mpr List.nodup_range').getElem_inj_iff.mp hequal
        exact Prod.ext (by omega) hrow
      · rintro rfl
        exact ⟨(hpoints _ _).mpr ⟨by omega, by omega, by simpa using hget⟩, rfl⟩
    simp [heq]
  obtain ⟨q, ⟨hq, hgraph⟩, _⟩ := seven_filling_permutation n combined hcombinedBounds
    (fun column hpositive hbound => (hfullFibers (fun cell => cell.1 = column)
      (hinsideColumns column)).trans
      (hpointsColumns column hpositive hbound))
    (fun row hpositive hbound => (hfullFibers (fun cell => cell.2 = row)
      (hinsideRows row)).trans
      (hpointsRows row hpositive hbound))
  have hinsideEqual : combined.filter (fun cell => cell ∈ activeRegion n p) = inside := by
    ext cell
    simp only [Finset.mem_filter, combined, Finset.mem_union]
    constructor
    · rintro ⟨hout | hin, hregion⟩
      · exact False.elim ((Finset.mem_filter.mp hout).2 hregion)
      · exact hin
    · intro hin
      exact ⟨Or.inr hin, hinsideRegion cell hin⟩
  have houtsideEqual : combined.filter (fun cell => cell ∉ activeRegion n p) = outside := by
    ext cell
    simp only [Finset.mem_filter, combined, Finset.mem_union]
    constructor
    · rintro ⟨hout | hin, hregion⟩
      · exact hout
      · exact False.elim (hregion (hinsideRegion cell hin))
    · intro hout
      exact ⟨Or.inl hout, (Finset.mem_filter.mp hout).2⟩
  have hpreserve := (active_geometry n p hp).2.2.2.2.1 points combined
    houtsideEqual.symm
    (fun row => by
      have heq : combined.filter (fun cell => cell ∈ activeRegion n p ∧ cell.2 = row) =
          inside.filter (fun cell => cell.2 = row) := by
        rw [← hinsideEqual, Finset.filter_filter]
      rw [heq]
      exact (hinsideRows row).symm)
    (fun column => by
      have heq : combined.filter (fun cell => cell ∈ activeRegion n p ∧ cell.1 = column) =
          inside.filter (fun cell => cell.1 = column) := by
        rw [← hinsideEqual, Finset.filter_filter]
      rw [heq]
      exact (hinsideColumns column).symm)
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
      exact Finset.mem_filter.mpr ⟨(hget _ _ (by omega) (by omega)).mpr (by simp),
        by omega, hpos.2⟩
    · intro first hfirst second hsecond hequal
      have := congrArg Prod.fst hequal
      omega
    · intro cell hcell
      obtain ⟨hcell, hwidthCell, hheightCell⟩ := Finset.mem_filter.mp hcell
      have hbound := hbounds cell hcell
      have hvalue := (hget _ _ hbound.1 hbound.2).mp hcell
      refine ⟨cell.1 - 1, ?_, ?_⟩
      · simp only [rectangle, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hvalue.trans_le hheightCell⟩
      · exact Prod.ext (by omega) hvalue
  have hpointsBounds : ∀ cell ∈ points, 1 ≤ cell.1 ∧ cell.1 ≤ n := by
    intro cell hcell
    exact ⟨((hpoints _ _).mp hcell).1, ((hpoints _ _).mp hcell).2.1⟩
  have hpointGraph : ∀ column row, 1 ≤ column → column ≤ n →
      ((column, row) ∈ points ↔ p.getD (column - 1) 0 = row) := by
    intro column row hpositive hbound
    simp only [hpoints, hpositive, hbound, true_and]
  have hcounts : ∀ maximum, 3 ≤ maximum → maximum ≤ n →
      (rectangle p (n - maximum + 3) maximum).card =
        (rectangle q (n - maximum + 3) maximum).card := by
    intro maximum hthree hbound
    rw [hrectangle p points hpointsBounds hpointGraph _ _ (by omega),
      hrectangle q combined (fun cell hcell =>
        ⟨(hcombinedBounds cell hcell).1, (hcombinedBounds cell hcell).2.1⟩)
        hgraph _ _ (by omega)]
    exact (hpreserve maximum hthree hbound).1
  have hregionEqual := (active_geometry n p hp).2.2.2.2.2.1 q hcounts
  have hentry : ∀ entry ∈ right,
      entry.2.2 = decide (q.getD (entry.1 - 1) 0 = entry.2.1) := by
    intro entry hentry
    have hcoordinate : (entry.1, entry.2.1) ∈ coordinates := by
      rw [← hrightShape]
      exact List.mem_map.mpr ⟨entry, hentry, rfl⟩
    have hregion := (hcoverage _).mp hcoordinate
    have hbound := hregionBounds _ hregion
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [← hgraph _ _ hbound.1 hbound.2.1]
    constructor
    · intro hbit
      exact Finset.mem_union.mpr (Or.inr (by
        simp only [inside, List.mem_toFinset, List.mem_map, List.mem_filter]
        exact ⟨entry, ⟨hentry, hbit⟩, rfl⟩))
    · intro hcombined
      have hin : (entry.1, entry.2.1) ∈ inside := by
        rw [← hinsideEqual]
        exact Finset.mem_filter.mpr ⟨hcombined, hregion⟩
      obtain ⟨other, ⟨hother, hbit⟩, hequal⟩ := by
        simpa only [inside, List.mem_toFinset, List.mem_map, List.mem_filter] using hin
      have heq : other = entry := List.inj_on_of_nodup_map hrightNodup
        hother hentry hequal
      simpa [heq] using hbit
  have htraceEqual : right = coordinates.map (fun cell =>
      (cell.1, cell.2, decide (q.getD (cell.1 - 1) 0 = cell.2))) := by
    rw [← hrightShape, List.map_map]
    conv_lhs => rw [← List.map_id right]
    apply List.map_congr_left
    intro entry hmem
    exact Prod.ext rfl (Prod.ext rfl (hentry entry hmem))
  refine ⟨q, axes, hq, ?_, haxesEmpty, ?_, ?_, hregionEqual.1.symm,
    hregionEqual.2.symm⟩
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
        ((filling.filter (fun cell => cell.2 = maximum ∧
          cell.1 ≤ n - maximum + 3)).Nonempty ↔
          ∃ position ∈ rectangle permutation (n - maximum + 3) maximum,
            permutation.getD position 0 = maximum) := by
      intro permutation filling hbounds hget
      constructor
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
        ((filling.filter (fun cell => cell.1 = n - maximum + 3 ∧
          cell.2 ≤ maximum)).Nonempty ↔
          n - maximum + 2 ∈ rectangle permutation (n - maximum + 3) maximum) := by
      intro permutation filling hget
      constructor
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

theorem seven_switch_involution (n : ℕ) :
    ∃ switch : {p : List ℕ // p.Perm (List.range' 1 n)} →
        {p : List ℕ // p.Perm (List.range' 1 n)},
      Function.Involutive switch ∧
      (∀ p, active n (switch p).val = active n p.val ∧
        activeRegion n (switch p).val = activeRegion n p.val) ∧
      (∀ p x y, 1 ≤ x → x ≤ n → (x, y) ∉ activeRegion n p.val →
        ((switch p).val.getD (x - 1) 0 = y ↔ p.val.getD (x - 1) 0 = y)) ∧
      (∀ p maximum, 3 ≤ maximum → maximum ≤ n →
        (rectangle (switch p).val (n - maximum + 3) maximum).card =
          (rectangle p.val (n - maximum + 3) maximum).card ∧
        ((∃ position ∈ rectangle (switch p).val (n - maximum + 3) maximum,
          (switch p).val.getD position 0 = maximum) ↔
          (∃ position ∈ rectangle p.val (n - maximum + 3) maximum,
            p.val.getD position 0 = maximum)) ∧
        (n - maximum + 2 ∈ rectangle (switch p).val (n - maximum + 3) maximum ↔
          n - maximum + 2 ∈ rectangle p.val (n - maximum + 3) maximum)) ∧
      (∀ p,
        let directions := sevenOutline (activeRegion n p.val) n 0 n
        sevenBoundary (fun x y => (sevenDiagram (switch p).val x y).getD .empty)
          0 directions =
            (sevenBoundary (fun x y => (sevenDiagram p.val x y).getD .empty)
              0 directions).map (fun step => (step.1, step.2.transpose))) := by
  classical
  let shape := fun p : {p : List ℕ // p.Perm (List.range' 1 n)} =>
    sevenOutline (activeRegion n p.val) n 0 n
  let labels := fun (p : {p : List ℕ // p.Perm (List.range' 1 n)}) x y =>
    (sevenDiagram p.val x y).getD SevenLabel.empty
  let boundary := fun p => sevenBoundary (labels p) 0 (shape p)
  let trace := fun (p : {p : List ℕ // p.Perm (List.range' 1 n)}) directions =>
    (sevenCells 0 directions).map (fun cell =>
      (cell.1, cell.2, decide (p.val.getD (cell.1 - 1) 0 = cell.2)))
  let conjugate := fun path : List (Bool × SevenLabel) =>
    path.map (fun step => (step.1, step.2.transpose))
  have hexists := fun p : {p : List ℕ // p.Perm (List.range' 1 n)} =>
    seven_switch_realization n p.val p.property
  dsimp only at hexists
  choose candidate axes hperm hcomputed hempty houtside hstats hactive hregion using hexists
  let switch := fun p => (⟨candidate p, hperm p⟩ :
    {p : List ℕ // p.Perm (List.range' 1 n)})
  have hshape : ∀ p, shape (switch p) = shape p := by
    intro p
    dsimp only [shape, switch]
    rw [hregion p]
  have hboundaryShape : ∀ directions column p,
      (sevenBoundary (labels p) column directions).map Prod.fst = directions := by
    intro directions
    induction directions with
    | nil => intro column p; rfl
    | cons direction tail ih =>
      intro column p
      cases direction <;> simp [sevenBoundary, ih]
  have htranspose : ∀ label : SevenLabel, label.transpose.transpose = label := by
    intro label
    cases label <;> rfl
  have hdouble : ∀ path, conjugate (conjugate path) = path := by
    intro path
    simp [conjugate, List.map_map, Function.comp_def, htranspose]
  have hedge : ∀ smaller larger : SevenLabel,
      sevenEdge smaller.transpose larger.transpose = sevenEdge smaller larger := by
    intro smaller larger
    cases smaller <;> cases larger <;> rfl
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
  have haxesEqual : ∀ (first second firstAxes secondAxes : List (Bool × SevenLabel))
      (firstTrace secondTrace : List (ℕ × ℕ × Bool)),
      sevenPath .empty first → sevenPath .empty second →
      first.map Prod.fst = second.map Prod.fst →
      sevenPeel .empty 0 first = some (firstAxes, firstTrace) →
      sevenPeel .empty 0 second = some (secondAxes, secondTrace) →
      (∀ step ∈ firstAxes, step.2 = .empty) →
      (∀ step ∈ secondAxes, step.2 = .empty) → firstAxes = secondAxes := by
    intro first second firstAxes secondAxes firstTrace secondTrace hfirst hsecond
      hshape hfirstPeel hsecondPeel hfirstEmpty hsecondEmpty
    obtain ⟨actualFirstAxes, actualFirstTrace, hactualFirst, _, hfirstSorted, hfirstPerm,
        _, _⟩ := seven_boundary_peeling .empty 0 first hfirst
    obtain ⟨actualSecondAxes, actualSecondTrace, hactualSecond, _, hsecondSorted,
        hsecondPerm, _, _⟩ := seven_boundary_peeling .empty 0 second hsecond
    have hfirstEq := Option.some.inj (hfirstPeel.symm.trans hactualFirst)
    have hsecondEq := Option.some.inj (hsecondPeel.symm.trans hactualSecond)
    have hfirstAxes : firstAxes = actualFirstAxes := (Prod.mk.inj hfirstEq).1
    have hsecondAxes : secondAxes = actualSecondAxes := (Prod.mk.inj hsecondEq).1
    rw [← hfirstAxes] at hfirstSorted hfirstPerm
    rw [← hsecondAxes] at hsecondSorted hsecondPerm
    have haxesShape : firstAxes.map Prod.fst = secondAxes.map Prod.fst := by
      apply List.Perm.eq_of_pairwise (le := fun first second : Bool =>
        first = false ∨ second = true)
      · intro first second hfirst hsecond hforward hbackward
        cases first <;> cases second <;> simp at hforward hbackward ⊢
      · simpa only [List.pairwise_map] using hfirstSorted
      · simpa only [List.pairwise_map] using hsecondSorted
      · rw [hshape] at hfirstPerm
        exact hfirstPerm.trans hsecondPerm.symm
    have hnormalize : ∀ path : List (Bool × SevenLabel),
        (∀ step ∈ path, step.2 = .empty) →
        path = path.map (fun step => (step.1, SevenLabel.empty)) := by
      intro path hall
      conv_lhs => rw [← List.map_id path]
      apply List.map_congr_left
      intro step hstep
      exact Prod.ext rfl (hall step hstep)
    rw [hnormalize firstAxes hfirstEmpty, hnormalize secondAxes hsecondEmpty]
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun direction => (direction, SevenLabel.empty))) haxesShape
  have hcompatibility : ∀ p, boundary (switch p) = conjugate (boundary p) := by
    intro p
    obtain ⟨_, _, _, hpPath, hpAxes, hpPeel, hpEmpty⟩ :=
      seven_active_boundary n p.val p.property
    obtain ⟨_, _, _, hqPath, hqAxes, hqPeel, hqEmpty⟩ :=
      seven_active_boundary n (switch p).val (switch p).property
    have hqComputed : sevenPeel .empty 0 (boundary (switch p)) =
        some (hqAxes, trace (switch p) (shape p)) := by
      have hread : sevenPeel .empty 0 (boundary (switch p)) =
          some (hqAxes, trace (switch p) (shape (switch p))) := hqPeel
      rw [hshape p] at hread
      exact hread
    have hpComputed : sevenPeel .empty 0 (conjugate (boundary p)) =
        some (axes p, trace (switch p) (shape p)) := hcomputed p
    have hpTransPath : sevenPath .empty (conjugate (boundary p)) := by
      simpa only [SevenLabel.transpose] using hconjugatePath (boundary p) .empty hpPath
    have hsameShape : (boundary (switch p)).map Prod.fst =
        (conjugate (boundary p)).map Prod.fst := by
      simp only [boundary, conjugate, List.map_map, Function.comp_def]
      rw [hboundaryShape, hboundaryShape, hshape p]
    have hsameAxes := haxesEqual (boundary (switch p)) (conjugate (boundary p))
      hqAxes (axes p) (trace (switch p) (shape p)) (trace (switch p) (shape p))
      hqPath hpTransPath hsameShape hqComputed hpComputed hqEmpty (hempty p)
    rw [hsameAxes] at hqComputed
    exact seven_peeling_unique .empty 0 (boundary (switch p)) (conjugate (boundary p))
      (axes p) (trace (switch p) (shape p)) hsameShape hqPath hpTransPath
      hqComputed hpComputed
  have hinvolutive : Function.Involutive switch := by
    intro p
    have htwiceBoundary : conjugate (boundary (switch p)) = boundary p := by
      rw [hcompatibility p, hdouble]
    obtain ⟨_, _, hcoverage, _, originalAxes, horiginal, _⟩ :=
      seven_active_boundary n p.val p.property
    have htwiceComputed : sevenPeel .empty 0 (boundary p) =
        some (axes (switch p), trace (switch (switch p)) (shape p)) := by
      have hread : sevenPeel .empty 0 (conjugate (boundary (switch p))) =
          some (axes (switch p), trace (switch (switch p)) (shape (switch p))) :=
        hcomputed (switch p)
      simpa only [htwiceBoundary, hshape p] using hread
    have htraceEqual : trace (switch (switch p)) (shape p) = trace p (shape p) :=
      congrArg Prod.snd (Option.some.inj (htwiceComputed.symm.trans horiginal))
    apply Subtype.ext
    have hlength : (switch (switch p)).val.length = p.val.length :=
      (switch (switch p)).property.length_eq.trans p.property.length_eq.symm
    apply List.ext_getElem hlength
    intro position hleft hright
    have hbound : position < n := by
      have := p.property.length_eq
      simp only [List.length_range'] at this
      omega
    have hvalue : (switch (switch p)).val.getD position 0 = p.val.getD position 0 := by
      by_cases hinside : (position + 1, p.val.getD position 0) ∈ activeRegion n p.val
      · have hcoordinate : (position + 1, p.val.getD position 0) ∈ sevenCells 0 (shape p) :=
          (hcoverage _).mpr hinside
        have hmem : (position + 1, p.val.getD position 0, true) ∈ trace p (shape p) := by
          apply List.mem_map.mpr
          exact ⟨(position + 1, p.val.getD position 0), hcoordinate, by simp⟩
        rw [← htraceEqual] at hmem
        obtain ⟨cell, _, heq⟩ := List.mem_map.mp hmem
        have hx := congrArg Prod.fst heq
        have hy := congrArg (fun entry => entry.2.1) heq
        have hbit := congrArg (fun entry => entry.2.2) heq
        change cell.1 = position + 1 at hx
        change cell.2 = p.val.getD position 0 at hy
        have hget := of_decide_eq_true hbit
        simpa only [hx, hy, Nat.add_sub_cancel] using hget
      · have hpOutside := houtside p (position + 1) (p.val.getD position 0)
          (by omega) (by omega) hinside
        have hqOutside := houtside (switch p) (position + 1) (p.val.getD position 0)
          (by omega) (by omega) (by
            change (position + 1, p.val.getD position 0) ∉ activeRegion n (candidate p)
            rw [hregion p]
            exact hinside)
        simpa only [Nat.add_sub_cancel] using hqOutside.mpr (hpOutside.mpr (by simp))
    simpa only [List.getD_eq_getElem (switch (switch p)).val 0 hleft,
      List.getD_eq_getElem p.val 0 hright] using hvalue
  refine ⟨switch, hinvolutive, ?_, houtside, hstats, ?_⟩
  · intro p
    exact ⟨hactive p, hregion p⟩
  · intro p
    simpa only [boundary, labels, hshape p] using hcompatibility p

theorem seven_corner_boundary (n : ℕ) (p : List ℕ)
    (hp : p.Perm (List.range' 1 n)) (maximum : ℕ) (hmaximum : maximum ∈ active n p) :
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
  have hgeometry := active_geometry n p hp
  have hcorner := hgeometry.2.2.2.1 maximum hmaximum
  have hdown := hgeometry.2.1
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

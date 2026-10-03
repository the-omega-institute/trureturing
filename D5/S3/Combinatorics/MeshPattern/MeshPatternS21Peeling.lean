/- GID: D5/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MeshPattern/MeshPatternS21Peeling
   mirror-E: none(waiver:elementary-boundary-peeling)
   anchors: []
   utility: none
   digest: Admissible seven-state boundaries peel to empty axes by local inversion. -/

import D5.S3.Combinatorics.MeshPattern.MeshPatternS21Seven

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MeshPattern.MeshPatternS21

def sevenPath (start : SevenLabel) : List (Bool × SevenLabel) → Prop
  | [] => True
  | (direction, next) :: tail =>
    (if direction then sevenEdge start next else sevenEdge next start) = true ∧
      sevenPath next tail

def sevenSlide (column : ℕ) (northwest northeast : SevenLabel) :
    List (Bool × SevenLabel) →
      Option (List (Bool × SevenLabel) × List (ℕ × ℕ × Bool))
  | [] => some ([(true, northeast)], [])
  | (true, next) :: tail => some ((true, northeast) :: (true, next) :: tail, [])
  | (false, southeast) :: tail => do
    let (southwest, entry) ← sevenInverse northeast northwest southeast
    let (boundary, cells) ← sevenSlide column southwest southeast tail
    some ((false, southwest) :: boundary,
      (column + 1, (tail.map Prod.fst).count false + 1, entry) :: cells)

def sevenPeel (start : SevenLabel) (column : ℕ) :
    List (Bool × SevenLabel) →
      Option (List (Bool × SevenLabel) × List (ℕ × ℕ × Bool))
  | [] => some ([], [])
  | (false, next) :: tail => do
    let (boundary, cells) ← sevenPeel next column tail
    some ((false, next) :: boundary, cells)
  | (true, next) :: tail => do
    let (boundary, cells) ← sevenPeel next (column + 1) tail
    let (axes, strip) ← sevenSlide column start next boundary
    some (axes, cells ++ strip)

def sevenRowWeight (start : SevenLabel) : List (Bool × SevenLabel) → ℕ → ℕ
  | [], _ => 0
  | (direction, next) :: tail, row =>
    (if direction = false ∧ row = (tail.map Prod.fst).count false + 1
      then start.size - next.size else 0) + sevenRowWeight next tail row

def sevenColumnWeight (start : SevenLabel) (column : ℕ) :
    List (Bool × SevenLabel) → ℕ → ℕ
  | [], _ => 0
  | (direction, next) :: tail, target =>
    (if direction = true ∧ target = column + 1 then next.size - start.size else 0) +
      sevenColumnWeight next (column + if direction then 1 else 0) tail target

def sevenArea : List Bool → ℕ
  | [] => 0
  | false :: tail => sevenArea tail
  | true :: tail => tail.count false + sevenArea tail

def sevenCells (column : ℕ) : List Bool → List (ℕ × ℕ)
  | [] => []
  | false :: tail => sevenCells column tail
  | true :: tail => sevenCells (column + 1) tail ++
    (List.range (tail.count false)).reverse.map (fun row => (column + 1, row + 1))

theorem seven_boundary_peeling (start : SevenLabel) (column : ℕ)
    (boundary : List (Bool × SevenLabel)) (hboundary : sevenPath start boundary) :
    ∃ axes cells, sevenPeel start column boundary = some (axes, cells) ∧
      sevenPath start axes ∧
      axes.Pairwise (fun first second => first.1 = false ∨ second.1 = true) ∧
      (axes.map Prod.fst).Perm (boundary.map Prod.fst) ∧
      axes.foldl (fun _ step => step.2) start =
        boundary.foldl (fun _ step => step.2) start ∧
      (start = .empty → boundary.foldl (fun _ step => step.2) start = .empty →
        ∀ step ∈ axes, step.2 = .empty) ∧
      cells.map (fun cell => (cell.1, cell.2.1)) =
        sevenCells column (boundary.map Prod.fst) := by
  have hlocal : ∀ northeast northwest southeast : SevenLabel,
      sevenEdge northwest northeast = true → sevenEdge southeast northeast = true →
      ∃ southwest entry, sevenInverse northeast northwest southeast = some (southwest, entry) ∧
        sevenForward southwest northwest southeast entry = some northeast ∧
        sevenEdge southwest northwest = true ∧ sevenEdge southwest southeast = true := by
    intro northeast northwest southeast hedgeNorth hedgeEast
    cases northeast <;> cases northwest <;> cases southeast <;>
      simp [sevenEdge] at hedgeNorth hedgeEast
    all_goals
      first
      | exact ⟨.empty, false, by decide⟩
      | exact ⟨.empty, true, by decide⟩
      | exact ⟨.one, false, by decide⟩
      | exact ⟨.one, true, by decide⟩
      | exact ⟨.twoRow, false, by decide⟩
      | exact ⟨.twoRow, true, by decide⟩
      | exact ⟨.twoCol, false, by decide⟩
      | exact ⟨.twoCol, true, by decide⟩
      | exact ⟨.threeRow, false, by decide⟩
      | exact ⟨.hook, false, by decide⟩
      | exact ⟨.threeCol, false, by decide⟩
  have hslide : ∀ tail : List (Bool × SevenLabel), ∀ northwest northeast column,
      sevenPath northwest ((true, northeast) :: tail) →
      tail.Pairwise (fun first second => first.1 = false ∨ second.1 = true) →
      ∃ axes cells, sevenSlide column northwest northeast tail = some (axes, cells) ∧
        sevenPath northwest axes ∧
        axes.Pairwise (fun first second => first.1 = false ∨ second.1 = true) ∧
        (axes.map Prod.fst).Perm (true :: tail.map Prod.fst) ∧
        axes.foldl (fun _ step => step.2) northwest =
          tail.foldl (fun _ step => step.2) northeast := by
    intro tail
    induction tail with
    | nil =>
      intro northwest northeast column hpath hsorted
      refine ⟨[(true, northeast)], [], rfl, hpath, ?_, ?_, rfl⟩
      · simp
      · exact List.Perm.refl _
    | cons step tail ih =>
      obtain ⟨direction, next⟩ := step
      cases direction with
      | false =>
        intro northwest northeast column hpath hsorted
        obtain ⟨hedge, hnext, htail⟩ := hpath
        obtain ⟨southwest, entry, hinverse, _, hleft, hbottom⟩ :=
          hlocal northeast northwest next hedge hnext
        obtain ⟨axes, cells, hcomputed, haxes, hsortedAxes, hperm, hlast⟩ :=
          ih southwest next column ⟨hbottom, htail⟩ (List.pairwise_cons.mp hsorted).2
        refine ⟨(false, southwest) :: axes,
          (column + 1, (tail.map Prod.fst).count false + 1, entry) :: cells,
          ?_, ?_, ?_, ?_, ?_⟩
        · simp [sevenSlide, hinverse, hcomputed]
        · exact ⟨hleft, haxes⟩
        · exact List.pairwise_cons.mpr ⟨fun _ _ => Or.inl rfl, hsortedAxes⟩
        · change (false :: axes.map Prod.fst).Perm (true :: false :: tail.map Prod.fst)
          exact (hperm.cons false).trans (List.Perm.swap _ _ _)
        · simpa using hlast
      | true =>
        intro northwest northeast column hpath hsorted
        refine ⟨(true, northeast) :: (true, next) :: tail, [], rfl, hpath, ?_, ?_, rfl⟩
        · apply List.pairwise_cons.mpr
          refine ⟨?_, hsorted⟩
          intro step hstep
          have : step.1 = true := by
            rcases List.mem_cons.mp hstep with rfl | hmem
            · rfl
            · have := (List.pairwise_cons.mp hsorted).1 step hmem
              simpa using this
          exact Or.inr this
        · exact List.Perm.refl _
  have hbuild : ∀ boundary : List (Bool × SevenLabel), ∀ start column,
      sevenPath start boundary →
      ∃ axes cells, sevenPeel start column boundary = some (axes, cells) ∧
        sevenPath start axes ∧
        axes.Pairwise (fun first second => first.1 = false ∨ second.1 = true) ∧
        (axes.map Prod.fst).Perm (boundary.map Prod.fst) ∧
        axes.foldl (fun _ step => step.2) start =
          boundary.foldl (fun _ step => step.2) start := by
    intro boundary
    induction boundary with
    | nil =>
      intro start column hpath
      exact ⟨[], [], rfl, trivial, List.Pairwise.nil, List.Perm.nil, rfl⟩
    | cons step tail ih =>
      obtain ⟨direction, next⟩ := step
      cases direction with
      | false =>
        intro start column hpath
        obtain ⟨hedge, htail⟩ := hpath
        obtain ⟨axes, cells, hcomputed, haxes, hsorted, hperm, hlast⟩ :=
          ih next column htail
        refine ⟨(false, next) :: axes, cells, ?_, ⟨hedge, haxes⟩, ?_, ?_, ?_⟩
        · simp [sevenPeel, hcomputed]
        · exact List.pairwise_cons.mpr ⟨fun _ _ => Or.inl rfl, hsorted⟩
        · exact hperm.cons false
        · simpa using hlast
      | true =>
        intro start column hpath
        obtain ⟨hedge, htail⟩ := hpath
        obtain ⟨axes, cells, hcomputed, haxes, hsorted, hperm, hlast⟩ :=
          ih next (column + 1) htail
        obtain ⟨output, strip, hslid, houtput, hsortedOutput, hpermOutput, hlastOutput⟩ :=
          hslide axes start next column ⟨hedge, haxes⟩ hsorted
        refine ⟨output, cells ++ strip, ?_, houtput, hsortedOutput, ?_, ?_⟩
        · simp [sevenPeel, hcomputed, hslid]
        · exact hpermOutput.trans (hperm.cons true)
        · simpa using hlastOutput.trans hlast
  have htraceSlide : ∀ tail : List (Bool × SevenLabel), ∀ northwest northeast column axes cells,
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
      cells.map (fun cell => (cell.1, cell.2.1)) = sevenCells column (path.map Prod.fst) := by
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
        obtain ⟨middle, points, hmiddle, _, _, _, _⟩ :=
          hbuild tail next column hpath.2
        simp only [sevenPeel, hmiddle, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq, Prod.mk.injEq] at hcomputed
        obtain ⟨rfl, rfl⟩ := hcomputed
        exact ih next column middle points hpath.2 hmiddle
      | true =>
        intro start column axes cells hpath hcomputed
        obtain ⟨middle, points, hmiddle, _, hsorted, hperm, _⟩ :=
          hbuild tail next (column + 1) hpath.2
        cases hslid : sevenSlide column start next middle with
        | none => simp [sevenPeel, hmiddle, hslid] at hcomputed
        | some output =>
          obtain ⟨remaining, strip⟩ := output
          simp only [sevenPeel, hmiddle, hslid, Option.bind_eq_bind, Option.bind_some,
            Option.some.injEq, Prod.mk.injEq] at hcomputed
          obtain ⟨rfl, rfl⟩ := hcomputed
          have hpoints := ih next (column + 1) middle points hpath.2 hmiddle
          have hstrip := htraceSlide middle start next column remaining strip hsorted hslid
          have hcount := hperm.count_eq false
          simp [sevenCells, List.map_append, hpoints, hstrip, hcount]
  obtain ⟨axes, cells, hcomputed, haxes, hsorted, hperm, hlast⟩ :=
    hbuild boundary start column hboundary
  refine ⟨axes, cells, hcomputed, haxes, hsorted, hperm, hlast, ?_,
    htrace boundary start column axes cells hboundary hcomputed⟩
  have hdown : ∀ label : SevenLabel, sevenEdge label .empty = true → label = .empty := by
    intro label
    cases label <;> decide
  have hzero : ∀ label : SevenLabel, label.size = 0 → label = .empty := by
    intro label
    cases label <;> decide
  have hmonotone : ∀ first second : SevenLabel,
      sevenEdge first second = true → first.size ≤ second.size := by
    intro first second
    cases first <;> cases second <;> decide
  have haxesEmpty : ∀ path : List (Bool × SevenLabel),
      sevenPath .empty path →
      path.Pairwise (fun first second => first.1 = false ∨ second.1 = true) →
      path.foldl (fun _ step => step.2) .empty = .empty →
      ∀ step ∈ path, step.2 = .empty := by
    intro path
    induction path with
    | nil => simp
    | cons step tail ih =>
      obtain ⟨direction, next⟩ := step
      cases direction with
      | false =>
        intro hpath hsorted hterminal
        obtain ⟨hedge, htail⟩ := hpath
        have : next = .empty := hdown next hedge
        subst next
        intro step hstep
        rcases List.mem_cons.mp hstep with rfl | hmem
        · rfl
        · exact ih htail (List.pairwise_cons.mp hsorted).2 hterminal step hmem
      | true =>
        intro hpath hsorted hterminal
        have hascending : ∀ path : List (Bool × SevenLabel), ∀ initial,
            sevenPath initial path → (∀ step ∈ path, step.1 = true) →
            initial.size ≤ (path.foldl (fun _ step => step.2) initial).size ∧
            ∀ step ∈ path, step.2.size ≤
              (path.foldl (fun _ step => step.2) initial).size := by
          intro path
          induction path with
          | nil => intro initial hpath hall; exact ⟨le_refl _, by simp⟩
          | cons step rest ih =>
            intro initial hpath hall
            obtain ⟨direction, next⟩ := step
            have hdirection := hall (direction, next) (by simp)
            dsimp at hdirection
            subst direction
            obtain ⟨hedge, hrest⟩ := hpath
            obtain ⟨hbound, hbounds⟩ := ih next hrest (by
              intro step hstep
              exact hall step (List.mem_cons_of_mem _ hstep))
            refine ⟨le_trans (hmonotone initial next hedge) hbound, ?_⟩
            intro step hstep
            rcases List.mem_cons.mp hstep with rfl | hmem
            · exact hbound
            · exact hbounds step hmem
        have hall : ∀ step ∈ (true, next) :: tail, step.1 = true := by
          intro step hstep
          rcases List.mem_cons.mp hstep with rfl | hmem
          · rfl
          · have := (List.pairwise_cons.mp hsorted).1 step hmem
            simpa using this
        have hbounds := (hascending ((true, next) :: tail) .empty hpath hall).2
        intro step hstep
        apply hzero
        have := hbounds step hstep
        rw [hterminal] at this
        exact Nat.le_zero.mp this
  intro hstart hterminal
  subst start
  apply haxesEmpty axes haxes hsorted
  exact hlast.trans hterminal

theorem seven_peeling_conservation (start : SevenLabel) (column : ℕ)
    (boundary axes : List (Bool × SevenLabel)) (cells : List (ℕ × ℕ × Bool))
    (hboundary : sevenPath start boundary)
    (hcomputed : sevenPeel start column boundary = some (axes, cells)) :
    (∀ row, sevenRowWeight start boundary row = sevenRowWeight start axes row +
      cells.countP (fun cell => cell.2.1 == row && cell.2.2)) ∧
    (∀ target, sevenColumnWeight start column boundary target =
      sevenColumnWeight start column axes target +
        cells.countP (fun cell => cell.1 == target && cell.2.2)) ∧
    (∀ row, cells.countP (fun cell => cell.2.1 == row && cell.2.2) ≤ 1) ∧
    (∀ target, cells.countP (fun cell => cell.1 == target && cell.2.2) ≤ 1) := by
  have hlocal : ∀ northeast northwest southeast southwest : SevenLabel, ∀ entry : Bool,
      sevenInverse northeast northwest southeast = some (southwest, entry) →
      sevenEdge southwest southeast = true ∧
      northeast.size - southeast.size =
        northwest.size - southwest.size + (if entry then 1 else 0) ∧
      northeast.size - northwest.size =
        southeast.size - southwest.size + (if entry then 1 else 0) := by
    intro northeast northwest southeast southwest entry hinverse
    cases northeast <;> cases northwest <;> cases southeast <;>
      simp only [sevenInverse, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hinverse
    all_goals
      obtain ⟨rfl, rfl⟩ := hinverse
      decide
  have hslide : ∀ tail : List (Bool × SevenLabel),
      ∀ northwest northeast column axes cells,
      sevenPath northwest ((true, northeast) :: tail) →
      sevenSlide column northwest northeast tail = some (axes, cells) →
      (axes.map Prod.fst).Perm (true :: tail.map Prod.fst) ∧
      (∀ row, sevenRowWeight northwest ((true, northeast) :: tail) row =
        sevenRowWeight northwest axes row +
          cells.countP (fun cell => cell.2.1 == row && cell.2.2)) ∧
      (∀ target, sevenColumnWeight northwest column ((true, northeast) :: tail) target =
        sevenColumnWeight northwest column axes target +
          cells.countP (fun cell => cell.1 == target && cell.2.2)) := by
    intro tail
    induction tail with
    | nil =>
      intro northwest northeast column axes cells hpath hcomputed
      simp only [sevenSlide, Option.some.injEq, Prod.mk.injEq] at hcomputed
      obtain ⟨rfl, rfl⟩ := hcomputed
      exact ⟨List.Perm.refl _, by simp, by simp⟩
    | cons step tail ih =>
      obtain ⟨direction, next⟩ := step
      cases direction with
      | true =>
        intro northwest northeast column axes cells hpath hcomputed
        simp only [sevenSlide, Option.some.injEq, Prod.mk.injEq] at hcomputed
        obtain ⟨rfl, rfl⟩ := hcomputed
        exact ⟨List.Perm.refl _, by simp, by simp⟩
      | false =>
        intro northwest northeast column axes cells hpath hcomputed
        cases hinverse : sevenInverse northeast northwest next with
        | none => simp [sevenSlide, hinverse] at hcomputed
        | some output =>
          obtain ⟨southwest, entry⟩ := output
          cases hrecursive : sevenSlide column southwest next tail with
          | none => simp [sevenSlide, hinverse, hrecursive] at hcomputed
          | some output =>
            obtain ⟨remaining, points⟩ := output
            simp only [sevenSlide, hinverse, hrecursive, Option.bind_eq_bind, Option.bind_some,
              Option.some.injEq, Prod.mk.injEq] at hcomputed
            obtain ⟨rfl, rfl⟩ := hcomputed
            obtain ⟨hbottom, hrow, hcolumn⟩ :=
              hlocal northeast northwest next southwest entry hinverse
            have hvalid : sevenPath southwest ((true, next) :: tail) :=
              ⟨hbottom, hpath.2.2⟩
            obtain ⟨hperm, hrows, hcolumns⟩ :=
              ih southwest next column remaining points hvalid hrecursive
            have hcount : (remaining.map Prod.fst).count false =
                (tail.map Prod.fst).count false := by
              have := hperm.count_eq false
              simpa using this
            refine ⟨(hperm.cons false).trans (List.Perm.swap _ _ _), ?_, ?_⟩
            · intro row
              have hbalance := hrows row
              by_cases hindex : row = (tail.map Prod.fst).count false + 1
              all_goals
                have hreverse : ((tail.map Prod.fst).count false + 1 = row) ↔
                    (row = (tail.map Prod.fst).count false + 1) := eq_comm
                cases entry <;>
                  simp [sevenRowWeight, hcount, hindex,
                    beq_iff_eq, hreverse] at hbalance hrow ⊢ <;> omega
            · intro target
              have hbalance := hcolumns target
              by_cases hindex : target = column + 1
              all_goals
                have hreverse : (column + 1 = target) ↔ (target = column + 1) := eq_comm
                cases entry <;>
                  simp [sevenColumnWeight, hindex,
                    beq_iff_eq, hreverse] at hbalance hcolumn ⊢ <;> omega
  have hstepBound : ∀ smaller larger : SevenLabel,
      sevenEdge smaller larger = true → larger.size - smaller.size ≤ 1 := by
    intro smaller larger
    cases smaller <;> cases larger <;> decide
  have hrowBound : ∀ path : List (Bool × SevenLabel), ∀ initial,
      sevenPath initial path → ∀ row,
      sevenRowWeight initial path row ≤ 1 ∧
        ((path.map Prod.fst).count false < row → sevenRowWeight initial path row = 0) := by
    intro path
    induction path with
    | nil => intro initial hpath row; simp [sevenRowWeight]
    | cons step tail ih =>
      obtain ⟨direction, next⟩ := step
      cases direction with
      | true =>
        intro initial hpath row
        simpa [sevenRowWeight] using ih next hpath.2 row
      | false =>
        intro initial hpath row
        have hrest := ih next hpath.2 row
        have hbound := hstepBound next initial hpath.1
        constructor
        · by_cases hindex : row = (tail.map Prod.fst).count false + 1
          · have hzero := hrest.2 (by omega)
            rw [sevenRowWeight, if_pos ⟨rfl, hindex⟩, hzero, Nat.add_zero]
            exact hbound
          · simpa [sevenRowWeight, hindex] using hrest.1
        · intro hsupport
          simp only [List.map_cons, List.count_cons, beq_self_eq_true, if_true] at hsupport
          have hindex : row ≠ (tail.map Prod.fst).count false + 1 := by omega
          have hzero := hrest.2 (by omega)
          simp [sevenRowWeight, hindex, hzero]
  have hcolumnBound : ∀ path : List (Bool × SevenLabel), ∀ initial column,
      sevenPath initial path → ∀ target,
      sevenColumnWeight initial column path target ≤ 1 ∧
        (target ≤ column ∨ column + (path.map Prod.fst).count true < target →
          sevenColumnWeight initial column path target = 0) := by
    intro path
    induction path with
    | nil => intro initial column hpath target; simp [sevenColumnWeight]
    | cons step tail ih =>
      obtain ⟨direction, next⟩ := step
      cases direction with
      | false =>
        intro initial column hpath target
        simpa [sevenColumnWeight] using ih next column hpath.2 target
      | true =>
        intro initial column hpath target
        have hrest := ih next (column + 1) hpath.2 target
        have hbound := hstepBound initial next hpath.1
        constructor
        · by_cases hindex : target = column + 1
          · have hzero := hrest.2 (Or.inl (by omega))
            rw [sevenColumnWeight, if_pos ⟨rfl, hindex⟩]
            change next.size - initial.size +
              sevenColumnWeight next (column + 1) tail target ≤ 1
            rw [hzero, Nat.add_zero]
            exact hbound
          · simpa [sevenColumnWeight, hindex] using hrest.1
        · intro hsupport
          simp only [List.map_cons, List.count_cons, beq_self_eq_true, if_true] at hsupport
          have hindex : target ≠ column + 1 := by omega
          have hzero := hrest.2 (by omega)
          simp [sevenColumnWeight, hindex, hzero]
  suffices hbalance :
      (∀ row, sevenRowWeight start boundary row = sevenRowWeight start axes row +
        cells.countP (fun cell => cell.2.1 == row && cell.2.2)) ∧
      (∀ target, sevenColumnWeight start column boundary target =
        sevenColumnWeight start column axes target +
          cells.countP (fun cell => cell.1 == target && cell.2.2)) by
    refine ⟨hbalance.1, hbalance.2, ?_, ?_⟩
    · intro row
      have := (hrowBound boundary start hboundary row).1
      have := hbalance.1 row
      omega
    · intro target
      have := (hcolumnBound boundary start column hboundary target).1
      have := hbalance.2 target
      omega
  induction boundary generalizing start column axes cells with
  | nil =>
    simp only [sevenPeel, Option.some.injEq, Prod.mk.injEq] at hcomputed
    obtain ⟨rfl, rfl⟩ := hcomputed
    exact ⟨by simp, by simp⟩
  | cons step tail ih =>
    obtain ⟨direction, next⟩ := step
    cases direction with
    | false =>
      obtain ⟨middle, points, hmiddle, _, _, hperm, _, _⟩ :=
        seven_boundary_peeling next column tail hboundary.2
      simp only [sevenPeel, hmiddle, Option.bind_eq_bind, Option.bind_some,
        Option.some.injEq, Prod.mk.injEq] at hcomputed
      obtain ⟨rfl, rfl⟩ := hcomputed
      obtain ⟨hrows, hcolumns⟩ := ih next column middle points hboundary.2 hmiddle
      have hcount := hperm.count_eq false
      constructor
      · intro row
        have := hrows row
        simp only [sevenRowWeight, hcount]
        omega
      · intro target
        simpa [sevenColumnWeight] using hcolumns target
    | true =>
      obtain ⟨middle, points, hmiddle, hvalid, _, _, _, _⟩ :=
        seven_boundary_peeling next (column + 1) tail hboundary.2
      cases hslid : sevenSlide column start next middle with
      | none => simp [sevenPeel, hmiddle, hslid] at hcomputed
      | some output =>
        obtain ⟨remaining, strip⟩ := output
        simp only [sevenPeel, hmiddle, hslid, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq, Prod.mk.injEq] at hcomputed
        obtain ⟨rfl, rfl⟩ := hcomputed
        obtain ⟨hrows, hcolumns⟩ :=
          ih next (column + 1) middle points hboundary.2 hmiddle
        obtain ⟨_, hstripRows, hstripColumns⟩ :=
          hslide middle start next column remaining strip ⟨hboundary.1, hvalid⟩ hslid
        constructor
        · intro row
          have hbalance := hrows row
          have hstripBalance := hstripRows row
          simp [sevenRowWeight, List.countP_append] at hstripBalance ⊢
          omega
        · intro target
          have hbalance := hcolumns target
          have hstripBalance := hstripColumns target
          simp [sevenColumnWeight, List.countP_append] at hstripBalance ⊢
          omega

theorem seven_peeling_unique (start : SevenLabel) (column : ℕ)
    (left right axes : List (Bool × SevenLabel)) (cells : List (ℕ × ℕ × Bool))
    (hshape : left.map Prod.fst = right.map Prod.fst)
    (hleft : sevenPath start left) (hright : sevenPath start right)
    (hleftComputed : sevenPeel start column left = some (axes, cells))
    (hrightComputed : sevenPeel start column right = some (axes, cells)) : left = right := by
  have hrecovery : ∀ northeast northwest southeast southwest : SevenLabel, ∀ entry : Bool,
      sevenInverse northeast northwest southeast = some (southwest, entry) →
      sevenForward southwest northwest southeast entry = some northeast := by
    intro northeast northwest southeast southwest entry hinverse
    cases northeast <;> cases northwest <;> cases southeast <;>
      simp only [sevenInverse, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hinverse
    all_goals
      obtain ⟨rfl, rfl⟩ := hinverse
      decide
  have hslideSize : ∀ tail : List (Bool × SevenLabel),
      ∀ northwest northeast column axes cells,
      tail.Pairwise (fun first second => first.1 = false ∨ second.1 = true) →
      sevenSlide column northwest northeast tail = some (axes, cells) →
      cells.length = (tail.map Prod.fst).count false := by
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
          obtain ⟨step, hstep, heq⟩ := List.mem_map.mp hmem
          have := (List.pairwise_cons.mp hsorted).1 step hstep
          simp [heq] at this
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
            simp only [sevenSlide, hinverse, hrecursive, Option.bind_eq_bind, Option.bind_some,
              Option.some.injEq, Prod.mk.injEq] at hcomputed
            obtain ⟨rfl, rfl⟩ := hcomputed
            have := ih southwest next column remaining points
              (List.pairwise_cons.mp hsorted).2 hrecursive
            simpa using this
  have hsize : ∀ boundary : List (Bool × SevenLabel), ∀ start column axes cells,
      sevenPath start boundary → sevenPeel start column boundary = some (axes, cells) →
      cells.length = sevenArea (boundary.map Prod.fst) := by
    intro boundary
    induction boundary with
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
          have hstrip := hslideSize middle start next column remaining strip hsorted hslid
          have hcount := hperm.count_eq false
          simp [sevenArea, List.length_append, hpoints, hstrip, hcount, Nat.add_comm]
  have hslideInjective : ∀ firstTail : List (Bool × SevenLabel),
      ∀ secondTail northwest firstNE secondNE column axes cells,
      firstTail.map Prod.fst = secondTail.map Prod.fst →
      sevenSlide column northwest firstNE firstTail = some (axes, cells) →
      sevenSlide column northwest secondNE secondTail = some (axes, cells) →
      firstNE = secondNE ∧ firstTail = secondTail := by
    intro firstTail
    induction firstTail with
    | nil =>
      intro secondTail northwest firstNE secondNE column axes cells hshape hfirst hsecond
      have : secondTail = [] := by simpa using hshape.symm
      subst secondTail
      have := hfirst.trans hsecond.symm
      simpa [sevenSlide] using this
    | cons firstStep firstTail ih =>
      intro secondTail northwest firstNE secondNE column axes cells hshape hfirst hsecond
      cases secondTail with
      | nil => simp at hshape
      | cons secondStep secondTail =>
        obtain ⟨direction, firstNext⟩ := firstStep
        obtain ⟨secondDirection, secondNext⟩ := secondStep
        have hdirs := List.cons.inj hshape
        dsimp at hdirs
        obtain ⟨rfl, htailShape⟩ := hdirs
        cases direction with
        | true =>
          have := hfirst.trans hsecond.symm
          simpa [sevenSlide, List.cons.injEq, Prod.mk.injEq] using this
        | false =>
          cases hinverseFirst : sevenInverse firstNE northwest firstNext with
          | none => simp [sevenSlide, hinverseFirst] at hfirst
          | some firstOutput =>
            obtain ⟨firstSW, firstEntry⟩ := firstOutput
            cases hinverseSecond : sevenInverse secondNE northwest secondNext with
            | none => simp [sevenSlide, hinverseSecond] at hsecond
            | some secondOutput =>
              obtain ⟨secondSW, secondEntry⟩ := secondOutput
              cases hrecursiveFirst : sevenSlide column firstSW firstNext firstTail with
              | none => simp [sevenSlide, hinverseFirst, hrecursiveFirst] at hfirst
              | some firstOutput =>
                obtain ⟨firstAxes, firstCells⟩ := firstOutput
                cases hrecursiveSecond : sevenSlide column secondSW secondNext secondTail with
                | none => simp [sevenSlide, hinverseSecond, hrecursiveSecond] at hsecond
                | some secondOutput =>
                  obtain ⟨secondAxes, secondCells⟩ := secondOutput
                  simp only [sevenSlide, hinverseFirst, hrecursiveFirst, Option.bind_eq_bind,
                    Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hfirst
                  simp only [sevenSlide, hinverseSecond, hrecursiveSecond, Option.bind_eq_bind,
                    Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hsecond
                  have haxesEq := List.cons.inj (hfirst.1.trans hsecond.1.symm)
                  have hcellsEq := List.cons.inj (hfirst.2.trans hsecond.2.symm)
                  have hswEq : firstSW = secondSW := congrArg Prod.snd haxesEq.1
                  have hentryEq : firstEntry = secondEntry :=
                    congrArg (fun cell => cell.2.2) hcellsEq.1
                  obtain ⟨rfl, rfl⟩ := And.intro haxesEq.2 hcellsEq.2
                  subst secondSW
                  subst secondEntry
                  obtain ⟨rfl, rfl⟩ := ih secondTail firstSW firstNext secondNext
                    column firstAxes firstCells htailShape hrecursiveFirst hrecursiveSecond
                  have hforwardFirst :=
                    hrecovery firstNE northwest firstNext firstSW firstEntry hinverseFirst
                  have hforwardSecond :=
                    hrecovery secondNE northwest firstNext firstSW firstEntry hinverseSecond
                  exact ⟨Option.some.inj (hforwardFirst.symm.trans hforwardSecond), rfl⟩
  induction left generalizing right start column axes cells with
  | nil => simpa using hshape.symm
  | cons firstStep firstTail ih =>
    cases right with
    | nil => simp at hshape
    | cons secondStep secondTail =>
      obtain ⟨direction, firstNext⟩ := firstStep
      obtain ⟨secondDirection, secondNext⟩ := secondStep
      have hdirs := List.cons.inj hshape
      dsimp at hdirs
      obtain ⟨rfl, htailShape⟩ := hdirs
      cases direction with
      | false =>
        obtain ⟨firstAxes, firstCells, hfirst, _, _, _, _, _⟩ :=
          seven_boundary_peeling firstNext column firstTail hleft.2
        obtain ⟨secondAxes, secondCells, hsecond, _, _, _, _, _⟩ :=
          seven_boundary_peeling secondNext column secondTail hright.2
        simp only [sevenPeel, hfirst, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq, Prod.mk.injEq] at hleftComputed
        simp only [sevenPeel, hsecond, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq, Prod.mk.injEq] at hrightComputed
        have haxesEq := List.cons.inj (hleftComputed.1.trans hrightComputed.1.symm)
        have hnextEq : firstNext = secondNext := congrArg Prod.snd haxesEq.1
        have hcellsEq := hleftComputed.2.trans hrightComputed.2.symm
        subst secondNext
        rw [← haxesEq.2, ← hcellsEq] at hsecond
        have := ih firstNext column secondTail firstAxes firstCells htailShape
          hleft.2 hright.2 hfirst hsecond
        simp [this]
      | true =>
        obtain ⟨firstAxes, firstCells, hfirst, _, hfirstSorted, hfirstPerm, _, _⟩ :=
          seven_boundary_peeling firstNext (column + 1) firstTail hleft.2
        obtain ⟨secondAxes, secondCells, hsecond, _, hsecondSorted, hsecondPerm, _, _⟩ :=
          seven_boundary_peeling secondNext (column + 1) secondTail hright.2
        have haxisShape : firstAxes.map Prod.fst = secondAxes.map Prod.fst := by
          apply List.Perm.eq_of_pairwise
            (le := fun first second : Bool => first = false ∨ second = true)
          · intro first second _ _ hforward hbackward
            have hantisymm : ∀ first second : Bool,
                (first = false ∨ second = true) → (second = false ∨ first = true) →
                first = second := by decide
            exact hantisymm first second hforward hbackward
          · exact List.pairwise_map.mpr hfirstSorted
          · exact List.pairwise_map.mpr hsecondSorted
          · rw [htailShape] at hfirstPerm
            exact hfirstPerm.trans hsecondPerm.symm
        cases hslidFirst : sevenSlide column start firstNext firstAxes with
        | none => simp [sevenPeel, hfirst, hslidFirst] at hleftComputed
        | some firstOutput =>
          obtain ⟨firstOutputAxes, firstStrip⟩ := firstOutput
          cases hslidSecond : sevenSlide column start secondNext secondAxes with
          | none => simp [sevenPeel, hsecond, hslidSecond] at hrightComputed
          | some secondOutput =>
            obtain ⟨secondOutputAxes, secondStrip⟩ := secondOutput
            simp only [sevenPeel, hfirst, hslidFirst, Option.bind_eq_bind, Option.bind_some,
              Option.some.injEq, Prod.mk.injEq] at hleftComputed
            simp only [sevenPeel, hsecond, hslidSecond, Option.bind_eq_bind, Option.bind_some,
              Option.some.injEq, Prod.mk.injEq] at hrightComputed
            have htraceLength : firstCells.length = secondCells.length := by
              rw [hsize firstTail firstNext (column + 1) firstAxes firstCells hleft.2 hfirst,
                hsize secondTail secondNext (column + 1) secondAxes secondCells hright.2 hsecond,
                htailShape]
            have htraceEq := hleftComputed.2.trans hrightComputed.2.symm
            obtain ⟨hpointsEq, hstripEq⟩ := List.append_inj htraceEq htraceLength
            have haxesEq := hleftComputed.1.trans hrightComputed.1.symm
            rw [← haxesEq, ← hstripEq] at hslidSecond
            obtain ⟨hnextEq, hmiddleEq⟩ := hslideInjective firstAxes secondAxes start
              firstNext secondNext column firstOutputAxes firstStrip haxisShape
              hslidFirst hslidSecond
            subst secondNext
            rw [← hmiddleEq, ← hpointsEq] at hsecond
            have := ih firstNext (column + 1) secondTail firstAxes firstCells htailShape
              hleft.2 hright.2 hfirst hsecond
            simp [this]

end D5.S3.Combinatorics.MeshPattern.MeshPatternS21

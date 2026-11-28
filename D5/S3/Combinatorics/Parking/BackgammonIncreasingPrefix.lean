/- GID: D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Parking/BackgammonIncreasingPrefix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First-car deletion and insertion for the backgammon parking outcome. -/

module

public import Init

@[expose] public section

namespace BackgammonIncreasingPrefix

abbrev Board := List (Option Nat)

/-- The first vacant slot, numbered from zero. -/
def firstVacancy : Board → Option Nat
  | [] => none
  | none :: _ => some 0
  | some _ :: slots => (firstVacancy slots).map Nat.succ

/-- The input preference is a zero-based index and the car label is one-based. -/
def arrive (board : Board) (preference car : Nat) : Board :=
  match board[preference]? with
  | none => board
  | some none => board.set preference (some car)
  | some (some incumbent) =>
    match firstVacancy board with
    | none => board
    | some vacancy => (board.set preference (some car)).set vacancy (some incumbent)

/-- The input preferences and the starting car label are one-based. -/
def parkFrom (board : Board) (car : Nat) (preferences : List Nat) : Board :=
  match preferences with
  | [] => board
  | preference :: rest => parkFrom (arrive board (preference - 1) car) (car + 1) rest

def emptyBoard (spots : Nat) : Board := List.replicate spots none

/-- Zero encodes vacancy. Under the theorem's hypotheses all spots are filled. -/
def backgammonOutcome (preferences : List Nat) : List Nat :=
  (parkFrom (emptyBoard preferences.length) 1 preferences).map (·.getD 0)

def Valid (preferences : List Nat) : Prop :=
  ∀ preference ∈ preferences, 1 ≤ preference ∧ preference ≤ preferences.length

/-- Process preferences up to the first repeat. -/
def distinctFrom (seen : List Nat) : List Nat → List Nat
  | [] => []
  | preference :: rest =>
    if preference ∈ seen then []
    else preference :: distinctFrom (preference :: seen) rest

def distinctPrefix (preferences : List Nat) : List Nat := distinctFrom [] preferences

def lifts (reduced : List Nat) : List (List Nat) :=
  let shifted := reduced.map Nat.succ
  (1 :: shifted) :: ((distinctPrefix reduced).map fun preference => (preference + 1) :: shifted)

theorem firstVacancy_spec (board : Board) (vacancy : Nat) :
    firstVacancy board = some vacancy ↔
      board[vacancy]? = some none ∧
      ∀ earlier, earlier < vacancy → ∃ car, board[earlier]? = some (some car) := by
  induction board generalizing vacancy with
  | nil => simp [firstVacancy]
  | cons slot rest ih =>
    cases slot with
    | none =>
      cases vacancy with
      | zero => simp [firstVacancy]
      | succ vacancy =>
        simp only [firstVacancy, Option.some.injEq, Nat.zero_ne_add_one, false_iff]
        intro h
        obtain ⟨car, hcar⟩ := h.2 0 (Nat.zero_lt_succ _)
        simp at hcar
    | some car =>
      cases vacancy with
      | zero => simp [firstVacancy]
      | succ vacancy =>
        simp only [firstVacancy, Option.map_eq_some_iff, Nat.succ.injEq, exists_eq_right,
          List.getElem?_cons_succ, ih]
        apply and_congr_right
        intro _
        constructor
        · intro h earlier hearlier
          cases earlier with
          | zero => exact ⟨car, rfl⟩
          | succ earlier => exact h earlier (Nat.lt_of_succ_lt_succ hearlier)
        · intro h earlier hearlier
          exact h (earlier + 1) (Nat.succ_lt_succ hearlier)

private theorem arrive_reserved_head (board : Board) (headCar preference car : Nat) :
    arrive (some headCar :: board) (preference + 1) car =
      some headCar :: arrive board preference car := by
  simp only [arrive, List.getElem?_cons_succ, firstVacancy, List.set_cons_succ]
  cases h : board[preference]? with
  | none => rfl
  | some slot =>
    cases slot with
    | none => rfl
    | some incumbent =>
      cases hv : firstVacancy board with
      | none => rfl
      | some vacancy => rfl

private theorem parkFrom_reserved_head (board : Board) (headCar car : Nat) (reduced : List Nat)
    (positive : ∀ preference ∈ reduced, 1 ≤ preference) :
    parkFrom (some headCar :: board) car (reduced.map Nat.succ) =
      some headCar :: parkFrom board car reduced := by
  induction reduced generalizing board car with
  | nil => rfl
  | cons p rest ih =>
    have hp := positive p List.mem_cons_self
    have hrest : ∀ preference ∈ rest, 1 ≤ preference :=
      fun preference h => positive preference (List.mem_cons_of_mem p h)
    have shift : p + 1 - 1 = (p - 1) + 1 := by omega
    simp only [List.map_cons, parkFrom]
    change parkFrom (arrive (some headCar :: board) (p + 1 - 1) car) (car + 1)
        (rest.map Nat.succ) = _
    rw [shift, arrive_reserved_head, ih _ _ hrest]

def vacancies (board : Board) : Nat := board.countP Option.isNone

private theorem firstVacancy_none (board : Board) :
    firstVacancy board = none ↔ vacancies board = 0 := by
  induction board with
  | nil => simp [firstVacancy, vacancies]
  | cons slot rest ih =>
    cases slot with
    | none => simp [firstVacancy, vacancies]
    | some car =>
      change (firstVacancy rest).map Nat.succ = none ↔
        (some car :: rest).countP Option.isNone = 0
      simpa only [Option.map_eq_none_iff, List.countP_cons, Option.isNone_some,
        Bool.false_eq_true, ite_false, Nat.add_zero, vacancies] using ih

private theorem arrive_length (board : Board) (preference car : Nat) :
    (arrive board preference car).length = board.length := by
  unfold arrive
  split
  · rfl
  · simp
  · split <;> simp

/-- Each legal arrival fills exactly one previously vacant spot. -/
private theorem arrive_vacancies (board : Board) (preference car : Nat)
    (inRange : preference < board.length) (room : 0 < vacancies board) :
    vacancies (arrive board preference car) = vacancies board - 1 := by
  cases hp : board[preference] with
  | none =>
    simp [arrive, List.getElem?_eq_getElem inRange, hp, vacancies, List.countP_set inRange]
  | some incumbent =>
    cases hv : firstVacancy board with
    | none => have := (firstVacancy_none board).mp hv; omega
    | some vacancy =>
      have vacant := ((firstVacancy_spec board vacancy).mp hv).1
      have vacancyBound : vacancy < board.length := by
        by_cases h : vacancy < board.length
        · exact h
        · rw [List.getElem?_eq_none (by omega)] at vacant
          cases vacant
      have distinct : preference ≠ vacancy := by
        intro equal
        subst vacancy
        rw [List.getElem?_eq_getElem inRange, hp] at vacant
        cases vacant
      have setBound : vacancy < (board.set preference (some car)).length := by
        simpa using vacancyBound
      have getVacant : board[vacancy] = none := by
        simpa [List.getElem?_eq_getElem vacancyBound] using vacant
      have setVacant : (board.set preference (some car))[vacancy] = none := by
        simpa [List.getElem_set_ne distinct] using getVacant
      simp [arrive, List.getElem?_eq_getElem inRange, hp, hv, vacancies,
        List.countP_set setBound, List.countP_set inRange, setVacant]

private theorem parkFrom_vacancies (board : Board) (car : Nat) (preferences : List Nat)
    (inRange : ∀ p ∈ preferences, 1 ≤ p ∧ p ≤ board.length)
    (room : preferences.length ≤ vacancies board) :
    vacancies (parkFrom board car preferences) = vacancies board - preferences.length := by
  induction preferences generalizing board car with
  | nil => simp [parkFrom]
  | cons p rest ih =>
    have hp := inRange p List.mem_cons_self
    have hp' : p - 1 < board.length := by omega
    have room' : 0 < vacancies board := by simp at room; omega
    have step := arrive_vacancies board (p - 1) car hp' room'
    have range' : ∀ q ∈ rest, 1 ≤ q ∧ q ≤ (arrive board (p - 1) car).length := by
      intro q hq
      rw [arrive_length]
      exact inRange q (List.mem_cons_of_mem p hq)
    have roomRest : rest.length ≤ vacancies (arrive board (p - 1) car) := by
      simp only [step]
      simp only [List.length_cons] at room
      omega
    simp only [parkFrom, ih _ _ range' roomRest, step, List.length_cons]
    omega

theorem outcomeBoard_full (preferences : List Nat) (valid : Valid preferences) :
    vacancies (parkFrom (emptyBoard preferences.length) 1 preferences) = 0 := by
  have count : vacancies (emptyBoard preferences.length) = preferences.length := by
    simp [vacancies, emptyBoard, List.countP_replicate]
  have range : ∀ p ∈ preferences, 1 ≤ p ∧ p ≤ (emptyBoard preferences.length).length := by
    simpa [emptyBoard, Valid] using valid
  simpa [count] using parkFrom_vacancies (emptyBoard preferences.length) 1 preferences range
    (by simp [count])

def relabel (board : Board) : Board := board.map (Option.map Nat.succ)

private theorem firstVacancy_relabel (board : Board) :
    firstVacancy (relabel board) = firstVacancy board := by
  induction board with
  | nil => rfl
  | cons slot rest ih =>
    cases slot with
    | none => rfl
    | some car =>
      change (firstVacancy (relabel rest)).map Nat.succ = _
      rw [ih]
      rfl

private theorem arrive_relabel (board : Board) (preference car : Nat) :
    arrive (relabel board) preference (car + 1) = relabel (arrive board preference car) := by
  have lookup : (relabel board)[preference]? = board[preference]?.map (Option.map Nat.succ) := by
    simp [relabel]
  simp only [arrive, firstVacancy_relabel, lookup]
  cases hp : board[preference]? with
  | none => rfl
  | some slot =>
    cases slot with
    | none => simp [relabel]
    | some incumbent =>
      cases hv : firstVacancy board <;> simp [relabel]

private theorem parkFrom_relabel (board : Board) (car : Nat) (preferences : List Nat) :
    parkFrom (relabel board) (car + 1) preferences =
      relabel (parkFrom board car preferences) := by
  induction preferences generalizing board car with
  | nil => rfl
  | cons p rest ih =>
    simp only [parkFrom, arrive_relabel, ih]

private theorem decode_relabel (board : Board) (noVacancies : vacancies board = 0) :
    (relabel board).map (·.getD 0) = (board.map (·.getD 0)).map Nat.succ := by
  simp only [relabel, List.map_map]
  apply List.map_congr_left
  intro slot hslot
  cases slot with
  | none =>
    have impossible := (List.countP_eq_zero.mp noVacancies) none hslot
    simp at impossible
  | some car => rfl

private theorem relabel_emptyBoard (length : Nat) :
    relabel (emptyBoard length) = emptyBoard length := by
  simp [relabel, emptyBoard]

/-- The first listed lift parks car 1 directly in spot 1. -/
private theorem firstCar_starts_in_first_spot (reduced : List Nat) (valid : Valid reduced) :
    backgammonOutcome (1 :: reduced.map Nat.succ) = 1 :: (backgammonOutcome reduced).map Nat.succ := by
  simp only [backgammonOutcome, List.length_cons, List.length_map]
  change (parkFrom (some 1 :: emptyBoard reduced.length) (1 + 1) (reduced.map Nat.succ)).map
    (·.getD 0) = _
  rw [parkFrom_reserved_head _ _ _ _ (fun p hp => (valid p hp).1)]
  rw [← relabel_emptyBoard reduced.length, parkFrom_relabel, relabel_emptyBoard]
  exact congrArg (1 :: ·) (decode_relabel _ (outcomeBoard_full reduced valid))

/-- Before the first collision the extra car occupies a slot still vacant in the reduced run. -/
def pendingBoard (board : Board) (pending : Nat) : Board :=
  none :: board.set pending (some 1)

/-- A fresh preference distinct from the pending slot preserves the pending comparison. -/
private theorem arrive_pending_fresh (board : Board) (pending preference car : Nat)
    (different : preference ≠ pending) (vacant : board[preference]? = some none) :
    arrive (pendingBoard board pending) (preference + 1) car =
      pendingBoard (arrive board preference car) pending := by
  simp only [pendingBoard, arrive, List.getElem?_cons_succ,
    List.getElem?_set_ne different.symm, vacant, List.set_cons_succ, List.cons.injEq, true_and]
  exact List.set_comm _ _ different.symm

/-- A match at the pending slot moves car 1 to the first spot and synchronizes both runs. -/
private theorem arrive_pending_match (board : Board) (pending car : Nat)
    (inRange : pending < board.length) (vacant : board[pending]? = some none) :
    arrive (pendingBoard board pending) (pending + 1) car =
      some 1 :: arrive board pending car := by
  have slot : board[pending] = none := by
    simpa [List.getElem?_eq_getElem inRange] using vacant
  simp [pendingBoard, arrive, inRange, slot, firstVacancy, List.set_set]

/-- An earlier collision elsewhere gives the first spot to the incumbent at that preference. -/
private theorem arrive_pending_collision (board : Board) (pending preference car incumbent : Nat)
    (different : preference ≠ pending) (occupied : board[preference]? = some (some incumbent)) :
    arrive (pendingBoard board pending) (preference + 1) car =
      some incumbent :: (board.set pending (some 1)).set preference (some car) := by
  simp [pendingBoard, arrive, List.getElem?_set_ne different.symm, occupied, firstVacancy]

private theorem arrive_first_spot (head : Option Nat) (board : Board) (car : Nat)
    (room : 0 < vacancies (head :: board)) :
    ∃ rest, arrive (head :: board) 0 car = some car :: rest := by
  cases head with
  | none => exact ⟨board, rfl⟩
  | some incumbent =>
    have roomTail : 0 < vacancies board := by simpa [vacancies] using room
    cases hv : firstVacancy board with
    | none =>
      have := (firstVacancy_none board).mp hv
      omega
    | some vacancy =>
      exact ⟨board.set vacancy (some incumbent), by simp [arrive, firstVacancy, hv]⟩

/-- A later label cannot be displaced into an already occupied first spot. -/
private theorem parkFrom_first_spot_ne_one (board : Board) (headCar car : Nat)
    (preferences : List Nat) (headNe : headCar ≠ 1) (later : 1 < car)
    (inRange : ∀ p ∈ preferences, 1 ≤ p ∧ p ≤ (some headCar :: board).length)
    (room : preferences.length ≤ vacancies (some headCar :: board)) :
    ∃ occupant rest, occupant ≠ 1 ∧
      parkFrom (some headCar :: board) car preferences = some occupant :: rest := by
  induction preferences generalizing board headCar car with
  | nil => exact ⟨headCar, board, headNe, rfl⟩
  | cons p rest ih =>
    have rangeP := inRange p List.mem_cons_self
    have indexRange : p - 1 < (some headCar :: board).length := by omega
    have positive : 0 < vacancies (some headCar :: board) := by
      simp only [List.length_cons] at room
      omega
    have step : ∃ occupant tail, occupant ≠ 1 ∧
        arrive (some headCar :: board) (p - 1) car = some occupant :: tail := by
      by_cases zero : p - 1 = 0
      · obtain ⟨tail, eq⟩ := arrive_first_spot (some headCar) board car positive
        exact ⟨car, tail, by omega, zero ▸ eq⟩
      · have shift : p - 1 = (p - 2) + 1 := by omega
        rw [shift, arrive_reserved_head]
        exact ⟨headCar, _, headNe, rfl⟩
    obtain ⟨occupant, newBoard, hoc, hstep⟩ := step
    have stepSize := arrive_length (some headCar :: board) (p - 1) car
    rw [hstep] at stepSize
    have stepVacancies := arrive_vacancies (some headCar :: board) (p - 1) car indexRange positive
    rw [hstep] at stepVacancies
    have validRest : ∀ q ∈ rest, 1 ≤ q ∧ q ≤ (some occupant :: newBoard).length := by
      intro q hq
      rw [stepSize]
      exact inRange q (List.mem_cons_of_mem p hq)
    have roomRest : rest.length ≤ vacancies (some occupant :: newBoard) := by
      simp only [List.length_cons] at room
      omega
    simpa only [parkFrom, hstep] using
      ih newBoard occupant (car + 1) hoc (by omega) validRest roomRest

private theorem parkFrom_no_late_first_preference (board : Board) (car : Nat)
    (preferences : List Nat) (later : 1 < car)
    (inRange : ∀ p ∈ preferences, 1 ≤ p ∧ p ≤ board.length)
    (room : preferences.length ≤ vacancies board)
    (finalHead : (parkFrom board car preferences).head? = some (some 1)) :
    ∀ p ∈ preferences, 1 < p := by
  induction preferences generalizing board car with
  | nil => simp
  | cons p rest ih =>
    have rangeP := inRange p List.mem_cons_self
    have indexRange : p - 1 < board.length := by omega
    have positive : 0 < vacancies board := by
      simp only [List.length_cons] at room
      omega
    let next := arrive board (p - 1) car
    have lengthNext : next.length = board.length := arrive_length _ _ _
    have nextVacancies : vacancies next = vacancies board - 1 :=
      arrive_vacancies _ _ _ indexRange positive
    have validRest : ∀ q ∈ rest, 1 ≤ q ∧ q ≤ next.length := by
      intro q hq
      rw [lengthNext]
      exact inRange q (List.mem_cons_of_mem p hq)
    have roomRest : rest.length ≤ vacancies next := by
      simp only [List.length_cons] at room
      omega
    have hp : 1 < p := by
      have pNotOne : p ≠ 1 := by
        intro hp
        subst p
        cases board with
        | nil => simp at rangeP
        | cons slot tail =>
          obtain ⟨updatedTail, headArrives⟩ := arrive_first_spot slot tail car positive
          have nextHead : next = some car :: updatedTail := headArrives
          rw [nextHead] at validRest roomRest
          obtain ⟨occupant, _, occupantNe, outcome⟩ := parkFrom_first_spot_ne_one updatedTail car
            (car + 1) rest (by omega) (by omega) validRest roomRest
          change (parkFrom next (car + 1) rest).head? = _ at finalHead
          rw [nextHead, outcome] at finalHead
          simp at finalHead
          exact occupantNe finalHead
      omega
    intro q hq
    rcases List.mem_cons.mp hq with same | tail
    · exact same.symm ▸ hp
    · exact ih next (car + 1) (by omega) validRest roomRest finalHead q tail

/-- Every later preference in a first-car fiber is strictly greater than 1. -/
private theorem firstCar_tail_preferences (word : List Nat) (valid : Valid word)
    (finalHead : (backgammonOutcome word).head? = some 1) :
    ∀ p ∈ word.tail, 1 < p := by
  cases word with
  | nil => simp
  | cons p rest =>
    have rangeP := valid p List.mem_cons_self
    let initial := emptyBoard (p :: rest).length
    have initialVacancies : vacancies initial = (p :: rest).length := by
      simp [initial, emptyBoard, vacancies, List.countP_replicate]
    have initialLength : initial.length = (p :: rest).length := by
      simp [initial, emptyBoard]
    let next := arrive initial (p - 1) 1
    have lengthNext : next.length = (p :: rest).length :=
      (arrive_length _ _ _).trans initialLength
    have validRest : ∀ q ∈ rest, 1 ≤ q ∧ q ≤ next.length := by
      intro q hq
      rw [lengthNext]
      exact valid q (List.mem_cons_of_mem p hq)
    have roomRest : rest.length ≤ vacancies next := by
      have step := arrive_vacancies initial (p - 1) 1
        (by rw [initialLength]; omega) (by simp [initialVacancies])
      change vacancies next = vacancies initial - 1 at step
      simp [step, initialVacancies]
    have rawHead : (parkFrom next 2 rest).head? = some (some 1) := by
      change ((parkFrom next 2 rest).map (·.getD 0)).head? = some 1 at finalHead
      rw [List.head?_map] at finalHead
      cases h : (parkFrom next 2 rest).head? with
      | none => simp [h] at finalHead
      | some slot =>
        cases slot with
        | none => simp [h] at finalHead
        | some car =>
          simpa [h] using finalHead
    exact parkFrom_no_late_first_preference next 2 rest (by decide) validRest roomRest rawHead

private theorem firstCar_reduced_valid (word : List Nat) (valid : Valid word)
    (finalHead : (backgammonOutcome word).head? = some 1) :
    Valid (word.tail.map fun p => p - 1) := by
  cases word with
  | nil => simp [Valid]
  | cons p rest =>
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    have positive := firstCar_tail_preferences (p :: rest) valid finalHead r hr
    have bound := (valid r (List.mem_cons_of_mem p hr)).2
    simp only [List.tail_cons, List.length_map, List.length_cons] at bound ⊢
    omega

/-- Prior to the first collision the occupied spots are the preferences already seen. -/
def BeforeCollision (board : Board) (seen : List Nat) : Prop :=
  ∀ p, 1 ≤ p → p ≤ board.length →
    if p ∈ seen then ∃ car, 1 < car ∧ board[p - 1]? = some (some car)
    else board[p - 1]? = some none

private theorem beforeCollision_fresh (board : Board) (seen : List Nat) (p car : Nat)
    (before : BeforeCollision board seen) (later : 1 < car)
    (positive : 1 ≤ p) (inRange : p ≤ board.length) (fresh : p ∉ seen) :
    BeforeCollision (arrive board (p - 1) car) (p :: seen) := by
  have vacant : board[p - 1]? = some none := by
    simpa [fresh] using before p positive inRange
  have index : p - 1 < board.length := by omega
  have update : arrive board (p - 1) car = board.set (p - 1) (some car) := by
    simp only [arrive, vacant]
  rw [update]
  intro q qPositive qBound
  simp only [List.length_set] at qBound
  by_cases eq : q = p
  · subst q
    simp only [List.mem_cons_self, ite_true]
    exact ⟨car, later, List.getElem?_set_self index⟩
  · have distinct : p - 1 ≠ q - 1 := by omega
    simpa only [List.mem_cons, eq, false_or, List.getElem?_set_ne distinct] using
      before q qPositive qBound

/-- The pending car reaches spot 1 exactly when its spot occurs before the first repeated
preference in the reduced run. In that case the two runs agree on every remaining spot. -/
private theorem parkFrom_pending (board : Board) (pending car : Nat) (preferences seen : List Nat)
    (before : BeforeCollision board seen) (notSeen : pending ∉ seen)
    (pendingPositive : 1 ≤ pending) (pendingBound : pending ≤ board.length)
    (later : 1 < car)
    (inRange : ∀ p ∈ preferences, 1 ≤ p ∧ p ≤ board.length)
    (room : preferences.length ≤ vacancies (pendingBoard board (pending - 1))) :
    let outcome := parkFrom (pendingBoard board (pending - 1)) car (preferences.map Nat.succ)
    ((outcome.head? = some (some 1)) ↔ pending ∈ distinctFrom seen preferences) ∧
      (pending ∈ distinctFrom seen preferences → outcome = some 1 :: parkFrom board car preferences) := by
  induction preferences generalizing board car seen with
  | nil => simp [parkFrom, pendingBoard, distinctFrom]
  | cons p rest ih =>
    have hp := inRange p List.mem_cons_self
    have pShift : p + 1 - 1 = (p - 1) + 1 := by omega
    let next := arrive (pendingBoard board (pending - 1)) ((p - 1) + 1) car
    have nextRoom : rest.length ≤ vacancies next := by
      have positive : 0 < vacancies (pendingBoard board (pending - 1)) := by
        simp only [List.length_cons] at room
        omega
      have bound : (p - 1) + 1 < (pendingBoard board (pending - 1)).length := by
        simp only [pendingBoard, List.length_cons, List.length_set]
        omega
      have count := arrive_vacancies (pendingBoard board (pending - 1)) ((p - 1) + 1) car
        bound positive
      change vacancies next = _ at count
      simp only [List.length_cons] at room
      omega
    simp only [List.map_cons, parkFrom, Nat.succ_eq_add_one, pShift]
    change ((parkFrom next (car + 1) (rest.map Nat.succ)).head? = some (some 1) ↔ _) ∧
      (_ → parkFrom next (car + 1) (rest.map Nat.succ) = _)
    by_cases seenP : p ∈ seen
    · obtain ⟨incumbent, incumbentLater, occupied⟩ := by
        simpa [seenP] using before p hp.1 hp.2
      have distinct : p - 1 ≠ pending - 1 := by
        intro equal
        have same : p = pending := by omega
        exact notSeen (same ▸ seenP)
      rw [show next = some incumbent :: _ from
        arrive_pending_collision board (pending - 1) (p - 1) car incumbent distinct occupied]
      have nextEq : next = some incumbent :: (board.set (pending - 1) (some 1)).set (p - 1)
          (some car) :=
        arrive_pending_collision board (pending - 1) (p - 1) car incumbent distinct occupied
      let tail := (board.set (pending - 1) (some 1)).set (p - 1) (some car)
      have rangeRest : ∀ q ∈ rest.map Nat.succ, 1 ≤ q ∧ q ≤ (some incumbent :: tail).length := by
        intro q hq
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
        have rr := inRange r (List.mem_cons_of_mem p hr)
        simp only [tail, List.length_cons, List.length_set]
        omega
      rw [nextEq] at nextRoom
      obtain ⟨occupant, remaining, wrong, headEq⟩ := parkFrom_first_spot_ne_one tail incumbent
        (car + 1) (rest.map Nat.succ) (by omega) (by omega) rangeRest (by simpa using nextRoom)
      change parkFrom (some incumbent :: _) (car + 1) (rest.map Nat.succ) = _ at headEq
      rw [headEq]
      simp [distinctFrom, seenP, wrong]
    · have vacant : board[p - 1]? = some none := by
        simpa [seenP] using before p hp.1 hp.2
      by_cases equal : p = pending
      · subst p
        have index : pending - 1 < board.length := by omega
        have step : next = some 1 :: arrive board (pending - 1) car :=
          arrive_pending_match board (pending - 1) car index vacant
        rw [step, parkFrom_reserved_head _ _ _ _ (fun q hq =>
          (inRange q (List.mem_cons_of_mem pending hq)).1)]
        simp [distinctFrom, seenP]
      · have distinct : p - 1 ≠ pending - 1 := by omega
        have step : next = pendingBoard (arrive board (p - 1) car) (pending - 1) :=
          arrive_pending_fresh board (pending - 1) (p - 1) car distinct vacant
        rw [step] at nextRoom ⊢
        have rangeRest : ∀ q ∈ rest, 1 ≤ q ∧ q ≤ (arrive board (p - 1) car).length := by
          intro q hq
          rw [arrive_length]
          exact inRange q (List.mem_cons_of_mem p hq)
        have notSeen' : pending ∉ p :: seen := by
          simpa [List.mem_cons, Ne.symm equal] using notSeen
        simpa [distinctFrom, seenP, Ne.symm equal] using
          ih (arrive board (p - 1) car) (car + 1) (p :: seen)
            (beforeCollision_fresh board seen p car before later hp.1 hp.2 seenP) notSeen'
            (by rw [arrive_length]; exact pendingBound) (by omega) rangeRest nextRoom

private theorem firstCar_bumped_to_first_spot (reduced : List Nat) (preference : Nat)
    (valid : Valid reduced) (positive : 1 ≤ preference) (bound : preference ≤ reduced.length) :
    let result := backgammonOutcome ((preference + 1) :: reduced.map Nat.succ)
    (result.head? = some 1 ↔ preference ∈ distinctPrefix reduced) ∧
      (preference ∈ distinctPrefix reduced →
        result = 1 :: (backgammonOutcome reduced).map Nat.succ) := by
  let board := emptyBoard reduced.length
  have emptyLookup (p : Nat) (h : p < reduced.length) : board[p]? = some none := by
    simp [board, emptyBoard, h]
  have size : board.length = reduced.length := by simp [board, emptyBoard]
  have pendingIndex : preference - 1 < board.length := by omega
  have vacancy : board[preference - 1] = none := by
    have i : preference - 1 < reduced.length := by omega
    simpa [List.getElem?_eq_getElem pendingIndex] using emptyLookup _ i
  have emptySeen : BeforeCollision board [] := by
    intro p hp hb
    have i : p - 1 < reduced.length := by omega
    simpa using emptyLookup (p - 1) i
  have emptyCount : vacancies board = reduced.length := by
    simp [board, vacancies, emptyBoard, List.countP_replicate]
  have room : reduced.length ≤ vacancies (pendingBoard board (preference - 1)) := by
    change reduced.length ≤
      (none :: board.set (preference - 1) (some 1)).countP Option.isNone
    change board.countP Option.isNone = reduced.length at emptyCount
    simp only [List.countP_cons, List.countP_set pendingIndex, vacancy, Option.isNone_none,
      Option.isNone_some, ite_true, Bool.false_eq_true, ite_false, Nat.add_zero, emptyCount]
    omega
  have parsed := parkFrom_pending board preference 2 reduced [] emptySeen (by simp) positive
    (by omega) (by decide) (by simpa only [size, Valid] using valid) room
  have step : arrive (none :: board) ((preference + 1) - 1) 1 =
      pendingBoard board (preference - 1) := by
    have rhs : preference + 1 - 1 = (preference - 1) + 1 := by omega
    have i : preference - 1 < reduced.length := by omega
    simp only [rhs, arrive, List.getElem?_cons_succ, emptyLookup _ i,
      List.set_cons_succ, pendingBoard]
  simp only [backgammonOutcome, List.length_cons, List.length_map]
  change (((parkFrom (arrive (none :: board) (preference + 1 - 1) 1) 2
      (reduced.map Nat.succ)).map (·.getD 0)).head? = some 1 ↔ _) ∧ (_ → _)
  rw [step]
  refine ⟨?_, ?_⟩
  · unfold distinctPrefix
    rw [← parsed.1]
    simp only [List.head?_map]
    cases (parkFrom (pendingBoard board (preference - 1)) 2
        (reduced.map Nat.succ)).head? with
    | none => simp
    | some slot =>
      cases slot <;> simp
  · intro inPrefix
    -- Expose the same initial arrival on the outcome side of the implication.
    change (parkFrom (arrive (none :: board) (preference + 1 - 1) 1) 2
        (reduced.map Nat.succ)).map (·.getD 0) = _
    rw [step, parsed.2 inPrefix]
    change 1 :: (parkFrom board 2 reduced).map (·.getD 0) =
      1 :: (List.map (·.getD 0) (parkFrom board 1 reduced)).map Nat.succ
    rw [show parkFrom board 2 reduced = relabel (parkFrom board 1 reduced) from by
      simpa only [board, relabel_emptyBoard] using parkFrom_relabel board 1 reduced]
    exact congrArg (1 :: ·) (decode_relabel _ (outcomeBoard_full reduced valid))

private theorem lift_head_membership (reduced : List Nat) (p : Nat) :
    (p :: reduced.map Nat.succ) ∈ lifts reduced ↔
      p = 1 ∨ ∃ q ∈ distinctPrefix reduced, q + 1 = p := by
  simp [lifts, List.mem_map]

private theorem lift_tail (word reduced : List Nat) (member : word ∈ lifts reduced) :
    word.tail = reduced.map Nat.succ := by
  simp only [lifts, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨_, _, rfl⟩ <;> rfl

/-- The lifts are exactly the valid words with the shifted tail and outcome. -/
theorem backgammon_first_car_insertion :
  ∀ word reduced : List Nat, Valid word → Valid reduced →
    (word ∈ lifts reduced ↔
      word.tail = reduced.map Nat.succ ∧
      backgammonOutcome word = 1 :: (backgammonOutcome reduced).map Nat.succ) := by
  intro word reduced validWord validReduced
  cases word with
  | nil => simp [lifts, backgammonOutcome, emptyBoard, parkFrom]
  | cons p rest =>
    by_cases shifted : rest = reduced.map Nat.succ
    · subst rest
      simp only [List.tail_cons, true_and, lift_head_membership]
      by_cases first : p = 1
      · subst p
        simp only [true_or, true_iff]
        exact firstCar_starts_in_first_spot reduced validReduced
      · have hp := validWord p List.mem_cons_self
        simp only [List.length_cons, List.length_map] at hp
        have hpos : 1 ≤ p - 1 := by omega
        have hbound : p - 1 ≤ reduced.length := by omega
        have hs : p - 1 + 1 = p := by omega
        have bumped := firstCar_bumped_to_first_spot reduced (p - 1) validReduced hpos hbound
        rw [hs] at bumped
        simp only [first, false_or]
        constructor
        · rintro ⟨q, hq, eq⟩
          have : q = p - 1 := by omega
          exact bumped.2 (this ▸ hq)
        · intro outcome
          have headEq : (backgammonOutcome (p :: reduced.map Nat.succ)).head? = some 1 :=
            congrArg List.head? outcome
          exact ⟨p - 1, bumped.1.mp headEq, hs⟩
    · exact ⟨fun member => False.elim (shifted (lift_tail _ _ member)),
        fun h => False.elim (shifted h.1)⟩

/-- A word with car 1 in spot 1 has the valid inverse obtained by deleting and shifting. -/
theorem backgammon_first_car_inverse :
  ∀ word : List Nat, Valid word → (backgammonOutcome word).head? = some 1 →
    (∀ preference ∈ word.tail, 1 < preference) ∧
    Valid (word.tail.map fun preference => preference - 1) ∧
    word ∈ lifts (word.tail.map fun preference => preference - 1) := by
  intro word valid outcome
  refine ⟨firstCar_tail_preferences word valid outcome,
    firstCar_reduced_valid word valid outcome, ?_⟩
  cases word with
  | nil => simp [backgammonOutcome, emptyBoard, parkFrom] at outcome
  | cons p rest =>
    let reduced := rest.map fun q => q - 1
    have validReduced : Valid reduced := firstCar_reduced_valid (p :: rest) valid outcome
    have shifted : reduced.map Nat.succ = rest := by
      simp only [reduced, List.map_map]
      calc
        _ = rest.map id := by
          apply List.map_congr_left
          intro q hq
          have := firstCar_tail_preferences (p :: rest) valid outcome q hq
          change q - 1 + 1 = q
          omega
        _ = _ := List.map_id rest
    change (p :: rest) ∈ lifts reduced
    rw [← shifted, lift_head_membership]
    by_cases first : p = 1
    · exact Or.inl first
    · have hp := valid p List.mem_cons_self
      have size : reduced.length = rest.length := by simp [reduced]
      have positive : 1 ≤ p - 1 := by omega
      have bound : p - 1 ≤ reduced.length := by
        simp only [List.length_cons] at hp
        omega
      have restore : p - 1 + 1 = p := by omega
      have bumped := firstCar_bumped_to_first_spot reduced (p - 1) validReduced positive bound
      rw [restore, shifted] at bumped
      exact Or.inr ⟨p - 1, bumped.1.mp outcome, restore⟩

private theorem distinctFrom_nodup_avoids (seen preferences : List Nat) :
    (distinctFrom seen preferences).Nodup ∧ ∀ p ∈ distinctFrom seen preferences, p ∉ seen := by
  induction preferences generalizing seen with
  | nil => simp [distinctFrom]
  | cons p rest ih =>
    by_cases seenP : p ∈ seen
    · simp [distinctFrom, seenP]
    · obtain ⟨nodup, avoids⟩ := ih (p :: seen)
      simp only [distinctFrom, seenP, ite_false, List.nodup_cons]
      refine ⟨⟨fun h => avoids p h List.mem_cons_self, nodup⟩, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with same | inTail
      · exact same.symm ▸ seenP
      · exact fun h => avoids q inTail (List.mem_cons_of_mem p h)

private theorem distinctFrom_succ (seen preferences : List Nat) :
    distinctFrom (seen.map Nat.succ) (preferences.map Nat.succ) =
      (distinctFrom seen preferences).map Nat.succ := by
  induction preferences generalizing seen with
  | nil => rfl
  | cons p rest ih =>
    have membership : p.succ ∈ seen.map Nat.succ ↔ p ∈ seen := by simp
    simp only [List.map_cons, distinctFrom, membership]
    split
    · rfl
    · rw [← List.map_cons, ih]
      rfl

private theorem distinctFrom_extra (seen larger : List Nat) (blocked : Nat)
    (preferences : List Nat)
    (membership : ∀ p, p ∈ larger ↔ p = blocked ∨ p ∈ seen) :
    distinctFrom larger preferences = (distinctFrom seen preferences).takeWhile (· != blocked) := by
  induction preferences generalizing seen larger with
  | nil => rfl
  | cons p rest ih =>
    have hp := membership p
    by_cases seenP : p ∈ seen
    · have inLarger := hp.mpr (Or.inr seenP)
      simp [distinctFrom, seenP, inLarger]
    · by_cases equal : p = blocked
      · subst p
        have inLarger := hp.mpr (Or.inl rfl)
        simp [distinctFrom, seenP, inLarger]
      · have notLarger : p ∉ larger := by simpa [hp, equal] using seenP
        simp [distinctFrom, notLarger, seenP, equal]
        congr 1
        apply ih
        intro q
        simp only [List.mem_cons, membership]
        constructor
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)

private theorem distinctPrefix_cons (p : Nat) (preferences : List Nat) :
    distinctPrefix (p :: preferences) =
      p :: (distinctPrefix preferences).takeWhile (· != p) := by
  simp only [distinctPrefix, distinctFrom, List.not_mem_nil, ite_false]
  rw [distinctFrom_extra [] [p] p preferences (by simp)]

private theorem takeWhile_ne_length_lt (prefs : List Nat) (p : Nat) (member : p ∈ prefs) :
    (prefs.takeWhile (· != p)).length < prefs.length := by
  induction prefs with
  | nil => simp at member
  | cons q rest ih =>
    by_cases same : q = p
    · simp [same]
    · have inTail : p ∈ rest := by simpa [Ne.symm same] using member
      simpa [List.takeWhile_cons, same] using ih inTail

private theorem takeWhile_ne_rank (prefs : List Nat) (nodup : prefs.Nodup) (index : Nat)
    (bound : index < prefs.length) :
    ∃ p, p ∈ prefs ∧ (prefs.takeWhile (· != p)).length = index ∧
      ∀ q, q ∈ prefs → (prefs.takeWhile (· != q)).length = index → q = p := by
  induction prefs generalizing index with
  | nil => simp at bound
  | cons head rest ih =>
    obtain ⟨notInTail, nodupTail⟩ := List.nodup_cons.mp nodup
    cases index with
    | zero =>
      refine ⟨head, List.mem_cons_self, by simp, ?_⟩
      intro q _ rank
      by_cases equal : head = q
      · exact equal.symm
      · simp [equal] at rank
    | succ index =>
      have tailBound : index < rest.length := Nat.lt_of_succ_lt_succ bound
      obtain ⟨p, hp, rankP, unique⟩ := ih nodupTail index tailBound
      have headNe : head ≠ p := fun h => notInTail (h.symm ▸ hp)
      refine ⟨p, List.mem_cons_of_mem head hp, by simpa [List.takeWhile_cons, headNe] using rankP, ?_⟩
      intro q hq rankQ
      have qNe : head ≠ q := by
        intro eq
        subst q
        simp at rankQ
      have tailMem : q ∈ rest := by simpa [Ne.symm qNe] using hq
      apply unique q tailMem
      simpa [List.takeWhile_cons, qNe] using rankQ

private theorem distinctFrom_mem (seen preferences : List Nat) (p : Nat)
    (member : p ∈ distinctFrom seen preferences) : p ∈ preferences := by
  induction preferences generalizing seen with
  | nil => simp [distinctFrom] at member
  | cons q rest ih =>
    by_cases seenQ : q ∈ seen
    · simp [distinctFrom, seenQ] at member
    · simp only [distinctFrom, seenQ, ite_false, List.mem_cons] at member
      exact member.elim (fun equal => List.mem_cons.mpr (Or.inl equal))
        (fun h => List.mem_cons_of_mem q (ih (q :: seen) h))

private theorem distinctFrom_take_spec (preferences seen : List Nat) (r : Nat)
    (bound : r ≤ preferences.length) :
    r ≤ (distinctFrom seen preferences).length ↔
      (preferences.take r).Nodup ∧ ∀ p ∈ preferences.take r, p ∉ seen := by
  induction preferences generalizing seen r with
  | nil =>
    have zero : r = 0 := by simpa using bound
    subst r
    simp [distinctFrom]
  | cons p rest ih =>
    cases r with
    | zero => simp
    | succ r =>
      by_cases seenP : p ∈ seen
      · simp [distinctFrom, seenP]
      · have restBound : r ≤ rest.length := Nat.le_of_succ_le_succ bound
        have scanned := ih (seen := p :: seen) (r := r) restBound
        simp only [distinctFrom, seenP, ite_false, List.length_cons, Nat.succ_le_succ_iff,
          scanned, List.take_succ_cons, List.nodup_cons]
        constructor
        · rintro ⟨nodup, avoids⟩
          refine ⟨⟨fun h => avoids p h List.mem_cons_self, nodup⟩, ?_⟩
          intro q hq belongs
          rcases List.mem_cons.mp hq with same | inTail
          · exact seenP (same ▸ belongs)
          · exact avoids q inTail (List.mem_cons_of_mem p belongs)
        · rintro ⟨⟨noP, nodup⟩, avoids⟩
          refine ⟨nodup, ?_⟩
          intro q hq inSeen
          rcases List.mem_cons.mp inSeen with same | old
          · exact noP (same ▸ hq)
          · exact avoids q (List.mem_cons_of_mem p hq) old

/-- The executable statistic gives the length of the longest pairwise-distinct prefix. -/
theorem distinctPrefix_length_spec (preferences : List Nat) (r : Nat)
    (bound : r ≤ preferences.length) :
    r ≤ (distinctPrefix preferences).length ↔ (preferences.take r).Nodup := by
  simpa [distinctPrefix] using distinctFrom_take_spec preferences [] r bound

private theorem distinctPrefix_shift (reduced : List Nat) :
    distinctPrefix (reduced.map Nat.succ) = (distinctPrefix reduced).map Nat.succ :=
  distinctFrom_succ [] reduced

private theorem lift_initial_length (reduced : List Nat) (valid : Valid reduced) :
    (distinctPrefix (1 :: reduced.map Nat.succ)).length = (distinctPrefix reduced).length + 1 := by
  rw [distinctPrefix_cons, distinctPrefix_shift, List.takeWhile_map]
  simp only [List.length_cons, List.length_map]
  have all (xs : List Nat) (positive : ∀ p ∈ xs, 1 ≤ p) :
      xs.takeWhile ((· != 1) ∘ Nat.succ) = xs := by
    induction xs with
    | nil => rfl
    | cons p rest ih =>
      have hp := positive p List.mem_cons_self
      have different : p ≠ 0 := by omega
      simp [Function.comp_apply, Nat.succ_eq_add_one, different,
        ih (fun q hq => positive q (List.mem_cons_of_mem p hq))]
  rw [all (distinctPrefix reduced) (fun p hp => (valid p (distinctFrom_mem [] reduced p hp)).1)]

private theorem lift_bumped_length (reduced : List Nat) (p : Nat) :
    (distinctPrefix ((p + 1) :: reduced.map Nat.succ)).length =
      ((distinctPrefix reduced).takeWhile (· != p)).length + 1 := by
  rw [distinctPrefix_cons, distinctPrefix_shift, List.takeWhile_map]
  have same : ((· != (p + 1)) ∘ Nat.succ) = (· != p) := by
    funext q
    simp [Function.comp_apply, Nat.succ_eq_add_one]
  simp [same]

/-- The longest distinct prefix length identifies each lift uniquely. -/
theorem backgammon_lift_statistic :
  ∀ reduced : List Nat, Valid reduced →
    (lifts reduced).Nodup ∧
    (∀ word ∈ lifts reduced,
      1 ≤ (distinctPrefix word).length ∧
        (distinctPrefix word).length ≤ (distinctPrefix reduced).length + 1) ∧
    ∀ r : Nat, 1 ≤ r → r ≤ (distinctPrefix reduced).length + 1 →
      ∃ word, word ∈ lifts reduced ∧ (distinctPrefix word).length = r ∧
        ∀ other, other ∈ lifts reduced → (distinctPrefix other).length = r → other = word := by
  intro reduced valid
  let freshPrefix := distinctPrefix reduced
  have prefixNodup : freshPrefix.Nodup := (distinctFrom_nodup_avoids [] reduced).1
  have baseRank := lift_initial_length reduced valid
  change (distinctPrefix (1 :: reduced.map Nat.succ)).length = freshPrefix.length + 1 at baseRank
  have bumpBelow (p : Nat) (member : p ∈ freshPrefix) :
      (distinctPrefix ((p + 1) :: reduced.map Nat.succ)).length < freshPrefix.length + 1 := by
    rw [lift_bumped_length]
    exact Nat.succ_lt_succ (takeWhile_ne_length_lt freshPrefix p member)
  refine ⟨?_, ?_, ?_⟩
  · simp only [lifts, List.nodup_cons, List.mem_map, List.cons.injEq]
    constructor
    · rintro ⟨p, member, eq, _⟩
      have hp := (valid p (distinctFrom_mem [] reduced p member)).1
      omega
    · rw [List.Nodup, List.pairwise_map]
      exact prefixNodup.imp (by
        intro p q different equal
        apply different
        have := (List.cons.inj equal).1
        omega)
  · intro word member
    simp only [lifts, List.mem_cons, List.mem_map] at member
    rcases member with rfl | ⟨p, hp, rfl⟩
    · rw [lift_initial_length reduced valid]
      exact ⟨Nat.succ_pos _, Nat.le_refl _⟩
    · exact ⟨by rw [lift_bumped_length]; exact Nat.succ_pos _,
        Nat.le_of_lt (bumpBelow p hp)⟩
  · intro r positive bound
    change r ≤ freshPrefix.length + 1 at bound
    by_cases last : r = freshPrefix.length + 1
    · refine ⟨1 :: reduced.map Nat.succ, by simp [lifts], baseRank.trans last.symm, ?_⟩
      intro other member rank
      simp only [lifts, List.mem_cons, List.mem_map] at member
      rcases member with rfl | ⟨p, hp, rfl⟩
      · rfl
      · have := bumpBelow p hp
        omega
    · have lower : r - 1 < freshPrefix.length := by omega
      have plus : r - 1 + 1 = r := by omega
      obtain ⟨p, inPrefix, pRank, unique⟩ := takeWhile_ne_rank freshPrefix prefixNodup (r - 1) lower
      refine ⟨(p + 1) :: reduced.map Nat.succ,
        (lift_head_membership reduced (p + 1)).mpr (Or.inr ⟨p, inPrefix, rfl⟩), ?_, ?_⟩
      · rw [lift_bumped_length, pRank, plus]
      · intro other member rank
        simp only [lifts, List.mem_cons, List.mem_map] at member
        rcases member with rfl | ⟨q, hq, rfl⟩
        · omega
        · rw [lift_bumped_length] at rank
          have qRank : (freshPrefix.takeWhile (· != q)).length = r - 1 := by
            change ((distinctPrefix reduced).takeWhile (· != q)).length = r - 1
            omega
          rw [unique q hq qRank]

/-- The lifted words lie on the street with one additional spot. -/
theorem lift_valid (word reduced : List Nat) (valid : Valid reduced)
    (member : word ∈ lifts reduced) : Valid word := by
  have validCons (p : Nat) (pRange : 1 ≤ p ∧ p ≤ reduced.length + 1) :
      Valid (p :: reduced.map Nat.succ) := by
    intro q hq
    simp only [List.length_cons, List.length_map]
    rcases List.mem_cons.mp hq with same | inTail
    · exact same.symm ▸ pRange
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp inTail
      have := valid r hr
      omega
  simp only [lifts, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨p, hp, rfl⟩
  · exact validCons 1 ⟨by decide, by omega⟩
  · have inside := valid p (distinctFrom_mem [] reduced p hp)
    exact validCons (p + 1) (by omega)

/-- The executable prefix length always lies within the preference word. -/
theorem distinctPrefix_length_le (preferences : List Nat) :
    (distinctPrefix preferences).length ≤ preferences.length := by
  have leLength (seen : List Nat) : (distinctFrom seen preferences).length ≤ preferences.length := by
    induction preferences generalizing seen with
    | nil => simp [distinctFrom]
    | cons p rest ih =>
      by_cases seenP : p ∈ seen
      · simp [distinctFrom, seenP]
      · simpa [distinctFrom, seenP] using ih (p :: seen)
  exact leLength []

-- The paper's Figure 3 and a run with both directions of displacement.
example : backgammonOutcome [1, 4, 4, 3, 2, 2] = [1, 6, 4, 3, 2, 5] := by decide
example : backgammonOutcome [3, 3, 1] = [3, 1, 2] := by decide
example : backgammonOutcome [] = [] := rfl

end BackgammonIncreasingPrefix

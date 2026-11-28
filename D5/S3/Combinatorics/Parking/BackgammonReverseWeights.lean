/- GID: D5/S3/Combinatorics/Parking/BackgammonReverseWeights
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Parking/BackgammonReverseWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact weighted recurrences for increasing-prefix and reverse backgammon outcomes. -/

module

public import D5.S3.Combinatorics.Parking.BackgammonIncreasingPrefix
import all D5.S3.Combinatorics.Parking.BackgammonIncreasingPrefix

@[expose] public section

/- The four-slot registration audit is unfinished. See https://github.com/the-omega-institute/trureturing/issues/35186. -/

namespace BackgammonIncreasingPrefix

/-- All words of a fixed length over the one-based alphabet `[spots]`. -/
def preferenceWords (spots : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | length + 1 => (List.range' 1 spots).flatMap fun p =>
      (preferenceWords spots length).map (p :: ·)

private theorem mem_preferenceWords (spots length : Nat) (word : List Nat) :
    word ∈ preferenceWords spots length ↔
      word.length = length ∧ ∀ p ∈ word, 1 ≤ p ∧ p ≤ spots := by
  induction length generalizing word with
  | zero => cases word <;> simp [preferenceWords]
  | succ length ih =>
    cases word with
    | nil => simp [preferenceWords]
    | cons p word =>
      rw [preferenceWords, List.mem_flatMap]
      constructor
      · rintro ⟨q, hq, member⟩
        obtain ⟨tail, ht, equal⟩ := List.mem_map.mp member
        cases equal
        obtain ⟨i, hi, eq⟩ := List.mem_range'.mp hq
        obtain ⟨hlen, bounds⟩ := (ih word).mp ht
        refine ⟨by simp [hlen], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact bounds x hx
      · rintro ⟨hlen, bounds⟩
        obtain ⟨lower, upper⟩ := bounds p List.mem_cons_self
        refine ⟨p, List.mem_range'.mpr ⟨p - 1, by omega, by omega⟩, ?_⟩
        exact List.mem_map.mpr ⟨word, (ih word).mpr
          ⟨by simpa using hlen, fun x hx => bounds x (List.mem_cons_of_mem p hx)⟩, rfl⟩

private theorem nodup_flatMap_of_unique {α β : Type} {xs : List α} {f : α → List β}
    (distinct : xs.Nodup) (fibers : ∀ x ∈ xs, (f x).Nodup)
    (unique : ∀ x ∈ xs, ∀ y ∈ xs, ∀ b ∈ f x, b ∈ f y → x = y) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at distinct
    rw [List.flatMap_cons, List.Nodup, List.pairwise_append]
    refine ⟨fibers x List.mem_cons_self, ih distinct.2
      (fun y hy => fibers y (List.mem_cons_of_mem x hy))
      (fun y hy z hz => unique y (List.mem_cons_of_mem x hy) z (List.mem_cons_of_mem x hz)), ?_⟩
    intro b hb c hc equal
    subst c
    obtain ⟨y, hy, hby⟩ := List.mem_flatMap.mp hc
    have xy := unique x List.mem_cons_self y (List.mem_cons_of_mem x hy) b hb hby
    exact distinct.1 (xy ▸ hy)

private theorem preferenceWords_nodup (spots length : Nat) :
    (preferenceWords spots length).Nodup := by
  induction length with
  | zero => simp [preferenceWords]
  | succ length ih =>
    apply nodup_flatMap_of_unique ((List.pairwise_lt_range' (s := 1) (n := spots)).imp
      (fun h => Nat.ne_of_lt h))
    · intro p _
      rw [List.Nodup, List.pairwise_map]
      exact ih.imp fun different equal => different (List.cons.inj equal).2
    · intro p _ q _ word hp hq
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
      obtain ⟨v, _, eq⟩ := List.mem_map.mp hq
      exact (List.cons.inj eq).1.symm

/-- All preference words with the specified outcome, without repetitions. -/
def outcomeWords (outcome : List Nat) : List (List Nat) :=
  (preferenceWords outcome.length outcome.length).filter
    (fun word => backgammonOutcome word == outcome)

theorem mem_outcomeWords (outcome word : List Nat) :
    word ∈ outcomeWords outcome ↔
      word.length = outcome.length ∧ Valid word ∧ backgammonOutcome word = outcome := by
  simp only [outcomeWords, List.mem_filter, beq_iff_eq, mem_preferenceWords, and_assoc]
  constructor
  · rintro ⟨hlen, hrange, hout⟩
    exact ⟨hlen, by simpa only [Valid, hlen] using hrange, hout⟩
  · rintro ⟨hlen, hvalid, hout⟩
    exact ⟨hlen, by simpa only [Valid, hlen] using hvalid, hout⟩

theorem outcomeWords_nodup (outcome : List Nat) : (outcomeWords outcome).Nodup :=
  List.Nodup.sublist List.filter_sublist (preferenceWords_nodup _ _)

/-- Insert car 1 in spot 1 and shift the labels of the remaining spots. -/
def shiftOutcome (outcome : List Nat) : List Nat := 1 :: outcome.map Nat.succ

private theorem lift_reduce (word reduced : List Nat) (member : word ∈ lifts reduced) :
    word.tail.map (· - 1) = reduced := by
  rw [lift_tail _ _ member, List.map_map]
  simp [Function.comp_def]

private theorem lift_length (word reduced : List Nat) (member : word ∈ lifts reduced) :
    word.length = reduced.length + 1 := by
  simp only [lifts, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨_, _, rfl⟩ <;> simp

/-- Every word in the shifted fiber is a lift of its unique reduced word. -/
theorem outcomeWords_shift_perm (outcome : List Nat) :
    (outcomeWords (shiftOutcome outcome)).Perm ((outcomeWords outcome).flatMap lifts) := by
  apply (List.perm_ext_iff_of_nodup (outcomeWords_nodup _) ?_).mpr
  · intro word
    rw [mem_outcomeWords, List.mem_flatMap]
    constructor
    · rintro ⟨hlen, valid, out⟩
      have head : (backgammonOutcome word).head? = some 1 := by simp [out, shiftOutcome]
      obtain ⟨_, validReduced, member⟩ := backgammon_first_car_inverse word valid head
      have outReduced := ((backgammon_first_car_insertion _ _ valid validReduced).mp member).2
      rw [out, shiftOutcome, List.cons.injEq] at outReduced
      have reducedLength := lift_length _ _ member
      have targetLength : (shiftOutcome outcome).length = outcome.length + 1 := by
        simp [shiftOutcome]
      refine ⟨_, (mem_outcomeWords _ _).mpr ⟨by omega, validReduced, ?_⟩, member⟩
      exact (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp outReduced.2.symm
    · rintro ⟨reduced, reducedMember, member⟩
      obtain ⟨hlen, validReduced, outReduced⟩ := (mem_outcomeWords _ _).mp reducedMember
      have valid := lift_valid word reduced validReduced member
      refine ⟨by rw [lift_length _ _ member, hlen]; simp [shiftOutcome], valid, ?_⟩
      rw [((backgammon_first_car_insertion _ _ valid validReduced).mp member).2, outReduced]
      rfl
  · apply nodup_flatMap_of_unique (outcomeWords_nodup _)
    · intro reduced member
      exact (backgammon_lift_statistic _ ((mem_outcomeWords _ _).mp member).2.1).1
    · intro left _ right _ word hleft hright
      exact (lift_reduce _ _ hleft).symm.trans (lift_reduce _ _ hright)

private abbrev prefixLength (word : List Nat) : Nat := (distinctPrefix word).length

private theorem lift_lengths_perm (word : List Nat) (valid : Valid word) :
    ((lifts word).map prefixLength).Perm (List.range' 1 (prefixLength word + 1)) := by
  obtain ⟨nodup, bounds, unique⟩ := backgammon_lift_statistic word valid
  have rangeNodup : (List.range' 1 (prefixLength word + 1)).Nodup :=
    (List.pairwise_lt_range').imp (fun h => Nat.ne_of_lt h)
  apply (List.perm_ext_iff_of_nodup ?_ rangeNodup).mpr
  · intro rank
    rw [List.mem_map, List.mem_range']
    constructor
    · rintro ⟨lift, member, rfl⟩
      obtain ⟨lower, upper⟩ := bounds lift member
      change 1 ≤ prefixLength lift at lower
      change prefixLength lift ≤ prefixLength word + 1 at upper
      exact ⟨prefixLength lift - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      change i < (distinctPrefix word).length + 1 at hi
      obtain ⟨lift, member, rank, _⟩ := unique (1 + 1 * i) (by omega) (by omega)
      exact ⟨lift, member, rank⟩
  · rw [List.Nodup, List.pairwise_map]
    apply nodup.imp_of_mem
    intro left right hl hr different equal
    obtain ⟨lower, upper⟩ := bounds left hl
    obtain ⟨selected, _, _, eq⟩ := unique (prefixLength left) lower upper
    exact different ((eq left hl rfl).trans (eq right hr equal.symm).symm)

/-- Count the words with a fixed outcome and a specified longest distinct prefix length. -/
def refinedCount (outcome : List Nat) (rank : Nat) : Nat :=
  (outcomeWords outcome).countP (fun word => (distinctPrefix word).length == rank)

/-- Adding car 1 in spot 1 contributes one word of rank `rank` from each reduced word
whose longest distinct prefix supports that rank. -/
theorem refinedCount_shift (outcome : List Nat) (rank : Nat) :
    refinedCount (shiftOutcome outcome) rank =
      (outcomeWords outcome).countP
        (fun word => decide (1 ≤ rank ∧ rank ≤ (distinctPrefix word).length + 1)) := by
  unfold refinedCount
  rw [(outcomeWords_shift_perm outcome).countP_eq, List.countP_flatMap]
  have count_fibers (words : List (List Nat)) (valid : ∀ word ∈ words, Valid word) :
      (words.map (List.countP (fun word => prefixLength word == rank) ∘ lifts)).sum =
        words.countP (fun word => decide (1 ≤ rank ∧ rank ≤ prefixLength word + 1)) := by
    induction words with
    | nil => rfl
    | cons reduced words ih =>
      rw [List.map_cons, List.sum_cons, List.countP_cons,
        ih (fun word member => valid word (List.mem_cons_of_mem reduced member))]
      have perm := lift_lengths_perm reduced (valid reduced List.mem_cons_self)
      have rangeNodup : (List.range' 1 (prefixLength reduced + 1)).Nodup :=
        (List.pairwise_lt_range').imp (fun h => Nat.ne_of_lt h)
      have count := perm.countP_eq (· == rank)
      rw [List.countP_map, ← List.count_eq_countP, rangeNodup.count] at count
      have rankIn : rank ∈ List.range' 1 (prefixLength reduced + 1) ↔
          1 ≤ rank ∧ rank ≤ prefixLength reduced + 1 := by
        rw [List.mem_range']
        constructor
        · rintro ⟨i, hi, eq⟩
          omega
        · rintro ⟨lower, upper⟩
          exact ⟨rank - 1, by omega, by omega⟩
      simp only [rankIn] at count
      change (lifts reduced).countP (fun word => prefixLength word == rank) =
        (if 1 ≤ rank ∧ rank ≤ prefixLength reduced + 1 then 1 else 0) at count
      rw [Function.comp_apply, count]
      simp [Nat.add_comm]
  exact count_fibers _ (fun word member => ((mem_outcomeWords _ _).mp member).2.1)

/-- Sum a weight over the positive prefix lengths attainable by one lift. -/
def liftWeight (weight : Nat → Nat) (length : Nat) : Nat :=
  ((List.range' 1 (length + 1)).map weight).sum

/-- Sum a weight depending only on the longest distinct preference prefix. -/
def outcomeWeight (outcome : List Nat) (weight : Nat → Nat) : Nat :=
  ((outcomeWords outcome).map (fun word => weight (distinctPrefix word).length)).sum

/-- Inserting one fixed car transforms any weight by summing it over the attainable ranks. -/
theorem outcomeWeight_shift (outcome : List Nat) (weight : Nat → Nat) :
    outcomeWeight (shiftOutcome outcome) weight = outcomeWeight outcome (liftWeight weight) := by
  unfold outcomeWeight
  rw [((outcomeWords_shift_perm outcome).map _).sum_nat, List.map_flatMap]
  have sum_fibers (words : List (List Nat)) (valid : ∀ word ∈ words, Valid word) :
      (words.flatMap (fun reduced => (lifts reduced).map
        (fun word => weight (prefixLength word)))).sum =
      (words.map (fun reduced => liftWeight weight (prefixLength reduced))).sum := by
    induction words with
    | nil => rfl
    | cons reduced words ih =>
      rw [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons,
        ih (fun word member => valid word (List.mem_cons_of_mem reduced member))]
      have fiber := ((lift_lengths_perm reduced (valid reduced List.mem_cons_self)).map weight).sum_nat
      rw [List.map_map] at fiber
      exact congrArg (· + _) fiber
  exact sum_fibers _ (fun word member => ((mem_outcomeWords _ _).mp member).2.1)

/-- The reverse suffix of length `length`, with one-based labels. -/
def reverseOutcome (length : Nat) : List Nat := (List.range' 1 length).reverse

/-- Put the fixed prefix of length `k` in front of the shifted outcome. -/
def withIncreasingPrefix : Nat → List Nat → List Nat
  | 0, outcome => outcome
  | k + 1, outcome => withIncreasingPrefix k (shiftOutcome outcome)

theorem withIncreasingPrefix_eq (k : Nat) (outcome : List Nat) :
    withIncreasingPrefix k outcome = List.range' 1 k ++ outcome.map (k + ·) := by
  induction k generalizing outcome with
  | zero => simp [withIncreasingPrefix]
  | succ k ih =>
    rw [withIncreasingPrefix, ih, shiftOutcome, List.map_cons, List.map_map,
      List.range'_concat, List.append_assoc]
    simp only [Nat.one_mul, Nat.add_comm 1 k, List.singleton_append]
    congr 1
    congr 1
    apply List.map_congr_left
    intro p _
    change k + (p + 1) = k + 1 + p
    omega

/-- Apply the one-car rank transform `k` times. -/
def iteratedLiftWeight : Nat → (Nat → Nat) → Nat → Nat
  | 0, weight => weight
  | k + 1, weight => liftWeight (iteratedLiftWeight k weight)

theorem outcomeWeight_increasingPrefix (k : Nat) (outcome : List Nat) (weight : Nat → Nat) :
    outcomeWeight (withIncreasingPrefix k outcome) weight =
      outcomeWeight outcome (iteratedLiftWeight k weight) := by
  induction k generalizing outcome with
  | zero => rfl
  | succ k ih => rw [withIncreasingPrefix, ih, outcomeWeight_shift, iteratedLiftWeight]

/-- The number of extensions through `k` inserted cars, for a reduced word of rank `length`. -/
def iteratedLiftCount (k length : Nat) : Nat := iteratedLiftWeight k (fun _ => 1) length

/-- Count the outcome of Question 5.2 by weighting each reverse-outcome word by its exact
number of extensions. The total street length is `k + suffixLength`. -/
theorem increasingPrefix_count (k suffixLength : Nat) :
    (outcomeWords (withIncreasingPrefix k (reverseOutcome suffixLength))).length =
      ((outcomeWords (reverseOutcome suffixLength)).map
        (fun word => iteratedLiftCount k (distinctPrefix word).length)).sum := by
  simpa [outcomeWeight, iteratedLiftCount, List.map_const', List.sum_replicate_nat] using
    (outcomeWeight_increasingPrefix k (reverseOutcome suffixLength) (fun _ => 1))


private theorem parkFrom_length (board : Board) (car : Nat) (word : List Nat) :
    (parkFrom board car word).length = board.length := by
  induction word generalizing board car with
  | nil => rfl
  | cons p rest ih => rw [parkFrom, ih, arrive_length]

private theorem parkFrom_append (board : Board) (car : Nat) (word rest : List Nat) :
    parkFrom board car (word ++ rest) =
      parkFrom (parkFrom board car word) (car + word.length) rest := by
  induction word generalizing board car with
  | nil => simp [parkFrom]
  | cons p word ih =>
    simp only [List.cons_append, parkFrom, ih, List.length_cons]
    congr 1
    omega

private theorem arrive_preference (board : Board) (p car : Nat)
    (bound : p < board.length) (room : 0 < vacancies board) :
    (arrive board p car)[p]? = some (some car) := by
  cases hp : board[p] with
  | none => simp [arrive, hp, bound]
  | some incumbent =>
    cases hv : firstVacancy board with
    | none => have := (firstVacancy_none board).mp hv; omega
    | some vacancy =>
      have vacant := ((firstVacancy_spec board vacancy).mp hv).1
      have ne : vacancy ≠ p := by
        intro eq
        subst vacancy
        simp [List.getElem?_eq_getElem bound, hp] at vacant
      simp [arrive, hp, hv, ne, bound]

/-- Occupied slots retain their label or acquire the current arrival's label. -/
private theorem arrive_occupied (board : Board) (p car i old : Nat)
    (occupied : board[i]? = some (some old)) :
    (arrive board p car)[i]? = some (some old) ∨
      (arrive board p car)[i]? = some (some car) := by
  have bound := List.getElem?_eq_some_iff.mp occupied
  unfold arrive
  split
  · exact Or.inl occupied
  · by_cases eq : p = i
    · subst p
      exact Or.inr (by simp [bound.1])
    · exact Or.inl (by simpa [List.getElem?_set_ne eq] using occupied)
  · rename_i incumbent hp
    split
    · exact Or.inl occupied
    · rename_i vacancy hv
      have vacant := ((firstVacancy_spec board vacancy).mp hv).1
      have ne : vacancy ≠ i := by
        intro eq
        subst vacancy
        rw [occupied] at vacant
        cases vacant
      rw [List.getElem?_set_ne ne]
      by_cases eq : p = i
      · subst p
        exact Or.inr (by simp [bound.1])
      · exact Or.inl (by simpa [List.getElem?_set_ne eq] using occupied)

private theorem parkFrom_occupied_ge (board : Board) (car : Nat) (word : List Nat)
    (i lower old : Nat) (occupied : board[i]? = some (some old))
    (oldBound : lower ≤ old) (carBound : lower ≤ car) :
    ∃ label, lower ≤ label ∧ (parkFrom board car word)[i]? = some (some label) := by
  induction word generalizing board car old with
  | nil => exact ⟨old, oldBound, occupied⟩
  | cons p rest ih =>
    rw [parkFrom]
    rcases arrive_occupied board (p - 1) car i old occupied with kept | replaced
    · exact ih _ _ _ kept oldBound (by omega)
    · exact ih _ _ _ replaced carBound (by omega)

/-- A preference for an in-range spot forces its final label to be at least the
starting car label. -/
private theorem parkFrom_preferred_ge (board : Board) (car : Nat) (word : List Nat)
    (readable : ∀ p ∈ word, 1 ≤ p ∧ p ≤ board.length) (room : word.length ≤ vacancies board)
    (p : Nat) (member : p ∈ word) :
    ∃ label, car ≤ label ∧ (parkFrom board car word)[p - 1]? = some (some label) := by
  induction word generalizing board car with
  | nil => simp at member
  | cons q rest ih =>
    have hq := readable q List.mem_cons_self
    have inRange : q - 1 < board.length := by omega
    have hasRoom : 0 < vacancies board := by simp at room; omega
    rw [parkFrom]
    rcases List.mem_cons.mp member with rfl | member
    · exact parkFrom_occupied_ge _ _ _ _ _ _
        (arrive_preference board (p - 1) car inRange hasRoom) (by omega) (by omega)
    · obtain ⟨label, above, atSpot⟩ := ih (arrive board (q - 1) car) (car + 1)
        (by simpa only [arrive_length] using
          fun pref hp => readable pref (List.mem_cons_of_mem q hp))
        (by rw [arrive_vacancies _ _ _ inRange hasRoom]; simp at room; omega) member
      exact ⟨label, by omega, atSpot⟩

private theorem firstVacancy_append_of_some (board suffix : Board) (i : Nat)
    (vacant : firstVacancy board = some i) :
    firstVacancy (board ++ suffix) = some i := by
  induction board generalizing i with
  | nil => simp [firstVacancy] at vacant
  | cons slot board ih =>
    cases slot with
    | none => simpa [firstVacancy] using vacant
    | some car =>
      simp only [firstVacancy, Option.map_eq_some_iff] at vacant
      obtain ⟨j, hj, rfl⟩ := vacant
      simp [firstVacancy, ih j hj]

private theorem arrive_append_of_room (board suffix : Board) (p car : Nat)
    (bound : p < board.length) (room : 0 < vacancies board) :
    arrive (board ++ suffix) p car = arrive board p car ++ suffix := by
  rw [arrive, arrive, List.getElem?_append_left bound]
  cases hp : board[p]? with
  | none => rfl
  | some slot =>
    cases slot with
    | none => simp [List.set_append_left, bound]
    | some incumbent =>
      cases hv : firstVacancy board with
      | none => have := (firstVacancy_none board).mp hv; omega
      | some i =>
        have hi := (List.getElem?_eq_some_iff.mp ((firstVacancy_spec board i).mp hv).1).1
        rw [firstVacancy_append_of_some _ _ _ hv, List.set_append_left _ _ bound]
        change ((board.set p (some car)) ++ suffix).set i (some incumbent) = _
        rw [List.set_append_left _ _ (by simpa using hi)]

/-- As long as the shorter street accommodates every arrival, any fixed
right-hand suffix of the board is inert. -/
private theorem parkFrom_append_of_room (board suffix : Board) (car : Nat) (word : List Nat)
    (readable : ∀ p ∈ word, 1 ≤ p ∧ p ≤ board.length) (room : word.length ≤ vacancies board) :
    parkFrom (board ++ suffix) car word = parkFrom board car word ++ suffix := by
  induction word generalizing board car with
  | nil => rfl
  | cons p rest ih =>
    have hp := readable p List.mem_cons_self
    have bound : p - 1 < board.length := by omega
    have hasRoom : 0 < vacancies board := by simp at room; omega
    rw [parkFrom, parkFrom, arrive_append_of_room _ _ _ _ bound hasRoom]
    apply ih
    · simpa only [arrive_length] using fun q hq => readable q (List.mem_cons_of_mem p hq)
    · rw [arrive_vacancies _ _ _ bound hasRoom]
      simp at room
      omega

private theorem reverseOutcome_cons (n : Nat) :
    reverseOutcome (n + 1) = (n + 1) :: reverseOutcome n := by
  simp [reverseOutcome, List.range'_concat, Nat.add_comm]

private theorem reverseOutcome_snoc (n : Nat) :
    reverseOutcome (n + 1) = (reverseOutcome n).map Nat.succ ++ [1] := by
  rw [reverseOutcome, List.range'_succ, List.reverse_cons]
  simp only [reverseOutcome, List.map_reverse, List.reverse_inj, List.append_left_inj]
  exact List.range'_succ_left (s := 1)

private theorem reverseOutcome_length (n : Nat) : (reverseOutcome n).length = n := by
  simp [reverseOutcome]

private theorem reverseOutcome_nodup (n : Nat) : (reverseOutcome n).Nodup := by
  rw [reverseOutcome, List.Nodup, List.pairwise_reverse]
  exact (List.pairwise_lt_range').imp (fun h => Ne.symm (Nat.ne_of_lt h))

private theorem emptyBoard_snoc (n : Nat) : emptyBoard (n + 1) = emptyBoard n ++ [none] := by
  simp [emptyBoard, List.replicate_succ']

/-- If car 1 finishes in the last spot, no other car can prefer that spot. -/
private theorem reverse_tail_range (p : Nat) (rest : List Nat) (valid : Valid (p :: rest))
    (out : backgammonOutcome (p :: rest) = reverseOutcome (rest.length + 1)) :
    ∀ q ∈ rest, 1 ≤ q ∧ q ≤ rest.length := by
  intro q hq
  obtain ⟨positive, bound⟩ := valid q (List.mem_cons_of_mem p hq)
  simp only [List.length_cons] at bound
  refine ⟨positive, Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne bound ?_)⟩
  intro equal
  subst q
  let board := emptyBoard (rest.length + 1)
  have pref := valid p List.mem_cons_self
  have inRange : p - 1 < board.length := by
    simp only [board, emptyBoard, List.length_replicate]
    simp only [List.length_cons] at pref
    omega
  have room : vacancies board = rest.length + 1 := by
    simp [board, vacancies, emptyBoard, List.countP_replicate]
  have roomAfter : rest.length ≤ vacancies (arrive board (p - 1) 1) := by
    rw [arrive_vacancies _ _ _ inRange (by omega), room]
    omega
  have readable : ∀ q ∈ rest, 1 ≤ q ∧ q ≤ (arrive board (p - 1) 1).length := by
    simpa [arrive_length, board, emptyBoard] using
      fun q hq => valid q (List.mem_cons_of_mem p hq)
  obtain ⟨label, lower, atSpot⟩ := parkFrom_preferred_ge _ 2 rest readable roomAfter _ hq
  have lookup := congrArg (fun xs : List Nat => xs[rest.length]?) out
  change ((parkFrom (arrive board (p - 1) 1) 2 rest).map (·.getD 0))[rest.length]? = _ at lookup
  have index : rest.length + 1 - 1 = rest.length := by omega
  rw [index] at atSpot
  rw [List.getElem?_map, atSpot, reverseOutcome_snoc, List.getElem?_append_right] at lookup
  · simp [reverseOutcome_length] at lookup
    omega
  · simp [reverseOutcome_length]


private theorem reverse_initial_last (rest : List Nat) (valid : Valid rest) :
    backgammonOutcome ((rest.length + 1) :: rest) =
      (backgammonOutcome rest).map Nat.succ ++ [1] := by
  have boardLength : (emptyBoard rest.length).length = rest.length := by simp [emptyBoard]
  have lookup : (emptyBoard rest.length ++ [none])[rest.length]? = some none := by
    rw [List.getElem?_append_right (by simp [boardLength]), boardLength, Nat.sub_self]
    rfl
  have start : arrive (emptyBoard rest.length ++ [none]) rest.length 1 =
      emptyBoard rest.length ++ [some 1] := by
    have bound : (emptyBoard rest.length).length ≤ rest.length := by simp [boardLength]
    rw [arrive, lookup]
    change (emptyBoard rest.length ++ [none]).set rest.length (some 1) = _
    rw [List.set_append_right _ _ bound, boardLength, Nat.sub_self]
    rfl
  simp only [backgammonOutcome, List.length_cons, emptyBoard_snoc, parkFrom, Nat.add_sub_cancel]
  rw [start, parkFrom_append_of_room]
  · rw [← relabel_emptyBoard rest.length, parkFrom_relabel, relabel_emptyBoard]
    rw [List.map_append, decode_relabel _ (outcomeBoard_full _ valid)]
    rfl
  · simpa only [boardLength, Valid] using valid
  · simp [vacancies, emptyBoard, List.countP_replicate]

private theorem firstVacancy_last (board : Board) (full : vacancies board = 0) :
    firstVacancy (board ++ [none]) = some board.length := by
  induction board with
  | nil => rfl
  | cons slot board ih =>
    cases slot with
    | none => simp [vacancies] at full
    | some car =>
      have fullTail : vacancies board = 0 := by
        simpa [vacancies, List.countP_cons] using full
      simp [firstVacancy, ih fullTail]

/-- The final arrival in a reverse fiber with a vacant last spot must prefer
spot 1 and move car 1 from there into the last spot. -/
private theorem reverse_final_arrival (initial : List Nat) (q : Nat) (valid : Valid initial)
    (nonempty : 0 < initial.length) (qRange : 1 ≤ q ∧ q ≤ initial.length + 1) :
    backgammonOutcome (initial ++ [q]) = reverseOutcome (initial.length + 1) ↔
      q = 1 ∧ backgammonOutcome initial = shiftOutcome (reverseOutcome (initial.length - 1)) := by
  let board := parkFrom (emptyBoard initial.length) 1 initial
  have size : board.length = initial.length := by simp [board, parkFrom_length, emptyBoard]
  have full : vacancies board = 0 := outcomeBoard_full initial valid
  have outcomeStep (q : Nat) : backgammonOutcome (initial ++ [q]) =
      (arrive (board ++ [none]) (q - 1) (initial.length + 1)).map (·.getD 0) := by
    simp only [backgammonOutcome, List.length_append, List.length_singleton, emptyBoard_snoc,
      parkFrom_append, parkFrom, Nat.add_comm 1]
    rw [parkFrom_append_of_room]
    · simpa [emptyBoard, Valid] using valid
    · simp [vacancies, emptyBoard, List.countP_replicate]
  have shifted : reverseOutcome (initial.length + 1) =
      (initial.length + 1) :: (reverseOutcome (initial.length - 1)).map Nat.succ ++ [1] := by
    rw [reverseOutcome_cons]
    have len : initial.length = (initial.length - 1) + 1 := by omega
    exact congrArg ((initial.length + 1) :: ·) (len ▸ reverseOutcome_snoc (initial.length - 1))
  have qEq (out : backgammonOutcome (initial ++ [q]) = reverseOutcome (initial.length + 1)) :
      q = 1 := by
    have atPref := arrive_preference (board ++ [none]) (q - 1) (initial.length + 1)
      (by simp [size]; omega) (by simp [vacancies])
    have atOut : (reverseOutcome (initial.length + 1))[q - 1]? = some (initial.length + 1) := by
      rw [← out, outcomeStep q, List.getElem?_map, atPref]
      rfl
    have atHead : (reverseOutcome (initial.length + 1))[0]? = some (initial.length + 1) := by
      simp [reverseOutcome_cons]
    have : 0 = q - 1 :=
      (List.Nodup.getElem?_inj (by simp [reverseOutcome_length])
        (reverseOutcome_nodup _) : _ ↔ 0 = q - 1).mp (atHead.trans atOut.symm)
    omega
  have afterPref :
      backgammonOutcome (initial ++ [1]) = reverseOutcome (initial.length + 1) ↔
        backgammonOutcome initial = shiftOutcome (reverseOutcome (initial.length - 1)) := by
    change _ ↔ board.map (·.getD 0) = _
    rw [outcomeStep 1, shifted]
    cases hb : board with
    | nil => simp [hb] at size; omega
    | cons slot tail =>
      cases slot with
      | none => simp [hb, vacancies] at full
      | some incumbent =>
        have vacancy := firstVacancy_last board full
        rw [hb] at vacancy
        have step : arrive ((some incumbent :: tail) ++ [none]) (1 - 1) (initial.length + 1) =
            (some (initial.length + 1) :: tail) ++ [some incumbent] := by
          unfold arrive
          change (match firstVacancy ((some incumbent :: tail) ++ [none]) with
            | none => (some incumbent :: tail) ++ [none]
            | some i => (some (initial.length + 1) :: (tail ++ [none])).set i
                (some incumbent)) = _
          rw [vacancy]
          change some (initial.length + 1) ::
            (tail ++ [none]).set tail.length (some incumbent) = _
          rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
          rfl
        rw [step]
        simp [List.map_append, List.cons_append, shiftOutcome, List.append_singleton_inj, and_comm]
  exact ⟨fun h => ⟨qEq h, afterPref.mp (qEq h ▸ h)⟩,
    fun ⟨equal, h⟩ => equal ▸ afterPref.mpr h⟩


private theorem mem_reverse_partition (m : Nat) (word : List Nat) :
    word ∈ outcomeWords (reverseOutcome (m + 2)) ↔
      word ∈ ((outcomeWords (reverseOutcome (m + 1))).map ((m + 2) :: ·)) ++
        ((outcomeWords (shiftOutcome (reverseOutcome m))).map (· ++ [1])) := by
  simp only [List.mem_append, List.mem_map, mem_outcomeWords, reverseOutcome_length]
  have shiftLength : (shiftOutcome (reverseOutcome m)).length = m + 1 := by
    simp [shiftOutcome, reverseOutcome_length]
  rw [shiftLength]
  constructor
  · rintro ⟨len, valid, out⟩
    cases word with
    | nil => simp at len
    | cons p rest =>
      have restLength : rest.length = m + 1 := by simp at len; omega
      have tailRange := reverse_tail_range p rest valid (by rw [restLength]; exact out)
      have restValid : Valid rest := tailRange
      by_cases last : p = m + 2
      · subst p
        rw [← show rest.length + 1 = m + 2 by omega, reverse_initial_last _ restValid,
          reverseOutcome_snoc, List.append_left_inj] at out
        rw [restLength] at out
        exact Or.inl ⟨rest, ⟨restLength, restValid,
          (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp out⟩, rfl⟩
      · have ne : rest ≠ [] := by intro h; simp [h] at restLength
        let initial := p :: rest.dropLast
        let q := rest.getLast ne
        have split : initial ++ [q] = p :: rest :=
          congrArg (p :: ·) (List.dropLast_concat_getLast ne)
        have initialLength : initial.length = m + 1 := by
          have len' := congrArg List.length split
          simp at len'
          omega
        have initialValid : Valid initial := by
          intro v hv
          rw [initialLength]
          rcases List.mem_cons.mp hv with same | mem
          · obtain ⟨positive, bound⟩ := valid p List.mem_cons_self
            simp only [List.length_cons, restLength] at bound
            exact ⟨by omega, by omega⟩
          · have inRest : v ∈ rest := by
              rw [← List.dropLast_concat_getLast ne]
              exact List.mem_append_left _ mem
            simpa only [restLength] using tailRange v inRest
        have qRange : 1 ≤ q ∧ q ≤ initial.length + 1 := by
          have h := valid q (by rw [← split]; simp)
          simpa only [List.length_cons, restLength, initialLength] using h
        have reverse := (reverse_final_arrival initial q initialValid (by omega) qRange).mp
          (by rw [split, initialLength]; exact out)
        refine Or.inr ⟨initial, ⟨initialLength, initialValid, ?_⟩, ?_⟩
        · simpa [initialLength] using reverse.2
        · rw [← reverse.1, split]
  · rintro (⟨rest, ⟨len, valid, out⟩, rfl⟩ | ⟨initial, ⟨len, valid, out⟩, rfl⟩)
    · refine ⟨by simp [len], ?_, ?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | mem
        · simp [len]
        · have h := valid v mem
          simp only [List.length_cons, len] at *
          omega
      · have size : m + 2 = rest.length + 1 := by omega
        rw [size, reverse_initial_last _ valid, reverseOutcome_snoc rest.length, len, out]
    · refine ⟨by simp [len], ?_, ?_⟩
      · intro v hv
        simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with mem | rfl
        · have h := valid v mem
          simp only [List.length_append, List.length_singleton]
          omega
        · simp
      · rw [← show initial.length + 1 = m + 2 by omega]
        apply (reverse_final_arrival initial 1 valid (by omega) (by omega)).mpr
        simpa [len] using out

/-- Reverse words split into those starting with the final spot and those whose
last arrival at spot 1 bumps car 1 into the final spot. -/
private theorem outcomeWords_reverse_perm (m : Nat) :
    (outcomeWords (reverseOutcome (m + 2))).Perm
      (((outcomeWords (reverseOutcome (m + 1))).map ((m + 2) :: ·)) ++
        ((outcomeWords (shiftOutcome (reverseOutcome m))).map (· ++ [1]))) := by
  apply (List.perm_ext_iff_of_nodup (outcomeWords_nodup _) ?_).mpr (mem_reverse_partition m)
  rw [List.nodup_append]
  refine ⟨(outcomeWords_nodup _).map _ (fun a b ne eq => ne (List.cons.inj eq).2),
    (outcomeWords_nodup _).map _ (fun a b ne eq => ne ((List.append_left_inj [1]).mp eq)), ?_⟩
  intro a ha b hb eq
  obtain ⟨rest, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨initial, hi, rfl⟩ := List.mem_map.mp hb
  obtain ⟨len, valid, _⟩ := (mem_outcomeWords _ _).mp hi
  have len' : initial.length = m + 1 := by simpa [shiftOutcome, reverseOutcome_length] using len
  have mem : m + 2 ∈ initial := by
    have belongs : m + 2 ∈ initial ++ [1] := eq ▸ List.mem_cons_self
    simpa using belongs
  have := (valid _ mem).2
  omega

private theorem prefixLength_cons_fresh (p : Nat) (word : List Nat) (fresh : p ∉ word) :
    prefixLength (p :: word) = prefixLength word + 1 := by
  rw [prefixLength, distinctPrefix_cons]
  have notIn : p ∉ distinctPrefix word := fun h => fresh (distinctFrom_mem [] word p h)
  have keep (xs : List Nat) (h : p ∉ xs) : xs.takeWhile (· != p) = xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      rw [List.mem_cons, not_or] at h
      simp [Ne.symm h.1, ih h.2]
  rw [keep _ notIn]
  rfl

private theorem prefixLength_snoc (word : List Nat) (valid : Valid word) (q : Nat)
    (qRange : 1 ≤ q ∧ q ≤ word.length) :
    prefixLength (word ++ [q]) = prefixLength word := by
  have wordBound := distinctPrefix_length_le word
  have snocBound : prefixLength (word ++ [q]) ≤ word.length := by
    apply Nat.le_of_not_gt
    intro h
    have nodup := (distinctPrefix_length_spec (word ++ [q]) (word.length + 1) (by simp)).mp h
    have full : (word ++ [q]).Nodup := by
      rwa [List.take_of_length_le (by simp)] at nodup
    have subset : word ++ [q] ⊆ List.range' 1 word.length := by
      intro v hv
      rw [List.mem_append, List.mem_singleton] at hv
      rcases hv with hw | rfl
      · have := valid v hw
        rw [List.mem_range'_1]
        omega
      · rw [List.mem_range'_1]
        omega
    have size := full.length_le_of_subset subset
    simp at size
    omega
  have agrees (r : Nat) (bound : r ≤ word.length) :
      r ≤ prefixLength (word ++ [q]) ↔ r ≤ prefixLength word := by
    rw [distinctPrefix_length_spec _ _ (by simp; omega), distinctPrefix_length_spec _ _ bound,
      List.take_append_of_le_length bound]
  exact Nat.le_antisymm ((agrees _ snocBound).mp (Nat.le_refl _))
    ((agrees _ wordBound).mpr (Nat.le_refl _))

/-- The reverse-outcome recurrence by longest distinct prefix, for arbitrary
weights on the prefix length. Both branches apply when the shorter word is empty. -/
theorem reverseOutcome_weight_succ_succ (m : Nat) (weight : Nat → Nat) :
    outcomeWeight (reverseOutcome (m + 2)) weight =
      outcomeWeight (reverseOutcome (m + 1)) (fun rank => weight (rank + 1)) +
        outcomeWeight (reverseOutcome m) (liftWeight weight) := by
  rw [← outcomeWeight_shift]
  unfold outcomeWeight
  rw [((outcomeWords_reverse_perm m).map _).sum_nat, List.map_append, List.sum_append,
    List.map_map, List.map_map]
  congr 1
  · apply congrArg List.sum
    apply List.map_congr_left
    intro word member
    obtain ⟨len, valid, _⟩ := (mem_outcomeWords _ _).mp member
    simp only [Function.comp_apply]
    change weight (prefixLength ((m + 2) :: word)) = weight (prefixLength word + 1)
    rw [prefixLength_cons_fresh]
    intro h
    have := (valid _ h).2
    rw [reverseOutcome_length] at len
    omega
  · apply congrArg List.sum
    apply List.map_congr_left
    intro word member
    obtain ⟨len, valid, _⟩ := (mem_outcomeWords _ _).mp member
    have len' : word.length = m + 1 := by simpa [shiftOutcome, reverseOutcome_length] using len
    simp only [Function.comp_apply]
    change weight (prefixLength (word ++ [1])) = weight (prefixLength word)
    rw [prefixLength_snoc _ valid _ (by omega)]


private theorem weight_indicator (outcome : List Nat) (predicate : Nat → Bool) :
    outcomeWeight outcome (fun rank => if predicate rank then 1 else 0) =
      (outcomeWords outcome).countP (predicate ∘ prefixLength) := by
  unfold outcomeWeight
  induction outcomeWords outcome with
  | nil => rfl
  | cons word words ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, Function.comp_apply, ih]
    split <;> simp [Nat.add_comm]

private theorem sum_map_add (xs : List Nat) (f g : Nat → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem countP_rank_tail (words : List (List Nat)) (rank m : Nat)
    (bound : ∀ word ∈ words, prefixLength word ≤ m) :
    words.countP (fun word => decide (rank ≤ prefixLength word)) =
      ((List.range' rank (m + 1 - rank)).map
        (fun r => words.countP (fun word => prefixLength word == r))).sum := by
  have weightSum (r : Nat) :
      (words.map (fun word => if r ≤ prefixLength word then 1 else 0)).sum =
        words.countP (fun word => decide (r ≤ prefixLength word)) := by
    induction words with
    | nil => rfl
    | cons word rest ih =>
      simp only [List.map_cons, List.sum_cons, List.countP_cons,
        ih (fun w hw => bound w (List.mem_cons_of_mem word hw)), decide_eq_true_eq]
      split <;> simp [Nat.add_comm]
  rw [← weightSum]
  clear weightSum
  induction words with
  | nil => simp [List.map_const', List.sum_replicate_nat]
  | cons word rest ih =>
    rw [List.map_cons, List.sum_cons, ih (fun w hw => bound w (List.mem_cons_of_mem word hw))]
    simp only [List.countP_cons]
    rw [sum_map_add]
    rw [Nat.add_comm]
    apply congrArg (_ + ·)
    have count :
        ((List.range' rank (m + 1 - rank)).map
          (fun r => if prefixLength word == r then 1 else 0)).sum =
            (List.range' rank (m + 1 - rank)).countP (· == prefixLength word) := by
      induction List.range' rank (m + 1 - rank) with
      | nil => rfl
      | cons r rs ihr =>
        simp only [List.map_cons, List.sum_cons, List.countP_cons, ihr]
        by_cases h : r = prefixLength word
        · subst r
          simp [Nat.add_comm]
        · have rev := Ne.symm h
          simp [h, rev]
    rw [count]
    have upper := bound word List.mem_cons_self
    by_cases h : rank ≤ prefixLength word
    · have inRange : prefixLength word ∈ List.range' rank (m + 1 - rank) := by
        rw [List.mem_range'_1]
        omega
      have nodup : (List.range' rank (m + 1 - rank)).Nodup :=
        (List.pairwise_lt_range').imp (fun h => Nat.ne_of_lt h)
      simp [← List.count_eq_countP, nodup.count, inRange, h]
    · have notIn : prefixLength word ∉ List.range' rank (m + 1 - rank) := by
        simp [List.mem_range'_1, h]
      have nodup : (List.range' rank (m + 1 - rank)).Nodup :=
        (List.pairwise_lt_range').imp (fun h => Nat.ne_of_lt h)
      simp [← List.count_eq_countP, nodup.count, notIn, h]

/-- Equation (5) of Clifton–Harris–Khaqan for the actual reverse parking fiber.
The first argument is the shorter suffix length and the output rank is `j + 1`. -/
theorem refinedCount_reverse_succ_succ (m j : Nat) :
    refinedCount (reverseOutcome (m + 2)) (j + 1) =
      refinedCount (reverseOutcome (m + 1)) j +
        ((List.range' j (m + 1 - j)).map (refinedCount (reverseOutcome m))).sum := by
  let w : Nat → Nat := fun rank => if rank == j + 1 then 1 else 0
  have hw := reverseOutcome_weight_succ_succ m w
  rw [← outcomeWeight_shift] at hw
  simp only [w] at hw
  rw [weight_indicator, weight_indicator, weight_indicator] at hw
  have shiftRank (r : Nat) : ((r + 1) == (j + 1)) = (r == j) := by simp
  simp only [Function.comp_def, shiftRank] at hw
  change refinedCount (reverseOutcome (m + 2)) (j + 1) =
    refinedCount (reverseOutcome (m + 1)) j +
      refinedCount (shiftOutcome (reverseOutcome m)) (j + 1) at hw
  rw [hw, refinedCount_shift]
  simp only [Nat.succ_le_succ_iff]
  apply congrArg (refinedCount (reverseOutcome (m + 1)) j + ·)
  exact countP_rank_tail _ _ _ (fun word member => by
    have len := ((mem_outcomeWords _ _).mp member).1
    rw [reverseOutcome_length] at len
    simpa [← len] using distinctPrefix_length_le word)

/-- A completely increasing outcome is obtained by extending the unique empty
preference word. This includes the empty street. -/
theorem increasingPrefix_count_diagonal (k : Nat) :
    (outcomeWords (withIncreasingPrefix k (reverseOutcome 0))).length =
      iteratedLiftCount k 0 := by
  rw [increasingPrefix_count]
  change ([[]].map (fun word => iteratedLiftCount k (distinctPrefix word).length)).sum = _
  simp [distinctPrefix, distinctFrom]

end BackgammonIncreasingPrefix

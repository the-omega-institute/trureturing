/- GID: D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary schedules track ordered occurrences from two fixed sources. -/

import D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketLeading

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder


variable {A : Type*}

inductive Side
  | first
  | second
  deriving DecidableEq

def annotateTwoFrom : Nat → Nat → List Side → List (Side × Nat)
  | _, _, [] => []
  | firstIndex, secondIndex, Side.first :: schedule =>
      (Side.first, firstIndex) ::
        annotateTwoFrom (firstIndex + 1) secondIndex schedule
  | firstIndex, secondIndex, Side.second :: schedule =>
      (Side.second, secondIndex) ::
        annotateTwoFrom firstIndex (secondIndex + 1) schedule

def annotateTwo : List Side → List (Side × Nat) :=
  annotateTwoFrom 0 0

/-- Offset both occurrence coordinates of an annotated binary schedule. -/
def shiftPairOccurrences (firstOffset secondOffset : Nat) :
    Side × Nat → Side × Nat
  | (Side.first, occurrence) => (Side.first, firstOffset + occurrence)
  | (Side.second, occurrence) => (Side.second, secondOffset + occurrence)

theorem annotateTwoFrom_add (firstOffset secondOffset : Nat)
    (schedule : List Side) (firstStart secondStart : Nat) :
    annotateTwoFrom (firstOffset + firstStart) (secondOffset + secondStart)
        schedule =
      (annotateTwoFrom firstStart secondStart schedule).map
        (shiftPairOccurrences firstOffset secondOffset) := by
  induction schedule generalizing firstStart secondStart with
  | nil => rfl
  | cons side schedule ih =>
      cases side with
      | first =>
          simp only [annotateTwoFrom, List.map_cons, shiftPairOccurrences]
          rw [← ih (firstStart + 1) secondStart]
          congr 2 <;> omega
      | second =>
          simp only [annotateTwoFrom, List.map_cons, shiftPairOccurrences]
          rw [← ih firstStart (secondStart + 1)]
          congr 2 <;> omega

private def swapSide : Side → Side
  | Side.first => Side.second
  | Side.second => Side.first

private def swapOccurrence : Side × Nat → Side × Nat
  | (side, i) => (swapSide side, i)

private theorem annotateTwoFrom_append (firstIndex secondIndex : Nat)
    (left right : List Side) :
    annotateTwoFrom firstIndex secondIndex (left ++ right) =
      annotateTwoFrom firstIndex secondIndex left ++
        annotateTwoFrom (firstIndex + left.count Side.first)
          (secondIndex + left.count Side.second) right := by
  induction left generalizing firstIndex secondIndex with
  | nil => simp [annotateTwoFrom]
  | cons side left ih =>
      cases side <;>
        simp [annotateTwoFrom, ih, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm]

private theorem annotateTwoFrom_swap (firstIndex secondIndex : Nat)
    (schedule : List Side) :
    annotateTwoFrom firstIndex secondIndex (schedule.map swapSide) =
      (annotateTwoFrom secondIndex firstIndex schedule).map swapOccurrence := by
  induction schedule generalizing firstIndex secondIndex with
  | nil => simp [annotateTwoFrom]
  | cons side schedule ih =>
      cases side <;> simp [annotateTwoFrom, swapSide, swapOccurrence, ih]

private theorem first_index_lt_count {firstIndex secondIndex i : Nat}
    {schedule : List Side}
    (hmem : (Side.first, i) ∈
      annotateTwoFrom firstIndex secondIndex schedule) :
    i < firstIndex + schedule.count Side.first := by
  induction schedule generalizing firstIndex secondIndex with
  | nil => simp [annotateTwoFrom] at hmem
  | cons side schedule ih =>
      cases side with
      | first =>
          simp only [annotateTwoFrom, List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · cases hmem
            simp
          · have := ih hmem
            simp only [List.count_cons, beq_self_eq_true, if_true]
            omega
      | second =>
          simp only [annotateTwoFrom, List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · cases hmem
          · simpa [List.count_cons, Side] using ih hmem

private theorem second_index_lt_count {firstIndex secondIndex i : Nat}
    {schedule : List Side}
    (hmem : (Side.second, i) ∈
      annotateTwoFrom firstIndex secondIndex schedule) :
    i < secondIndex + schedule.count Side.second := by
  induction schedule generalizing firstIndex secondIndex with
  | nil => simp [annotateTwoFrom] at hmem
  | cons side schedule ih =>
      cases side with
      | first =>
          simp only [annotateTwoFrom, List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · cases hmem
          · simpa [List.count_cons, Side] using ih hmem
      | second =>
          simp only [annotateTwoFrom, List.mem_cons] at hmem
          rcases hmem with hmem | hmem
          · cases hmem
            simp
          · have := ih hmem
            simp only [List.count_cons, beq_self_eq_true, if_true]
            omega

private theorem second_count_gt_first_count (schedule : List Side)
    (hstarts : schedule.head? = some Side.second)
    (hnoBalance : ∀ left right,
      schedule = left ++ right → left ≠ [] →
        left.count Side.first ≠ left.count Side.second) :
    schedule.count Side.first < schedule.count Side.second := by
  obtain ⟨tail, rfl⟩ : ∃ tail, schedule = Side.second :: tail := by
    cases schedule with
    | nil => simp at hstarts
    | cons side tail =>
        simp only [List.head?_cons, Option.some.injEq] at hstarts
        exact ⟨tail, by simpa [hstarts]⟩
  have walk : ∀ (tail : List Side) (firstCount secondCount : Nat),
      firstCount < secondCount →
      (∀ left right, tail = left ++ right →
        firstCount + left.count Side.first ≠
          secondCount + left.count Side.second) →
      firstCount + tail.count Side.first <
        secondCount + tail.count Side.second := by
    intro tail
    induction tail with
    | nil =>
        intro firstCount secondCount hlt _
        simpa using hlt
    | cons side tail ih =>
        intro firstCount secondCount hlt hnever
        have hstepNe := hnever [side] tail (by simp)
        cases side with
        | first =>
            have hstep : firstCount + 1 < secondCount := by
              simp [Side] at hstepNe
              omega
            have htail : ∀ left right, tail = left ++ right →
                (firstCount + 1) + left.count Side.first ≠
                  secondCount + left.count Side.second := by
              intro left right heq
              have := hnever (Side.first :: left) right (by simp [heq])
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              ih (firstCount + 1) secondCount hstep htail
        | second =>
            have hstep : firstCount < secondCount + 1 := by omega
            have htail : ∀ left right, tail = left ++ right →
                firstCount + left.count Side.first ≠
                  (secondCount + 1) + left.count Side.second := by
              intro left right heq
              have := hnever (Side.second :: left) right (by simp [heq])
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              ih firstCount (secondCount + 1) hstep htail
  have hnever : ∀ left right, tail = left ++ right →
      0 + left.count Side.first ≠ 1 + left.count Side.second := by
    intro left right heq
    have := hnoBalance (Side.second :: left) right (by simp [heq]) (by simp)
    simpa [Nat.add_comm] using this
  simpa [Nat.add_comm] using walk tail 0 1 (by omega) hnever

private theorem first_return_or_always_ahead (schedule : List Side)
    (hstarts : schedule.head? = some Side.second) :
    (∃ lead suffix,
      schedule = lead ++ suffix ∧ lead ≠ [] ∧
      lead.count Side.first = lead.count Side.second ∧
      ∀ left right, lead = left ++ right → left ≠ [] → right ≠ [] →
        left.count Side.first < left.count Side.second) ∨
    (∀ left right, schedule = left ++ right → left ≠ [] →
      left.count Side.first < left.count Side.second) := by
  classical
  by_cases hex : ∃ n, 0 < n ∧ n ≤ schedule.length ∧
      (schedule.take n).count Side.first =
        (schedule.take n).count Side.second
  · let r := Nat.find hex
    have hr := Nat.find_spec hex
    have hrMinimal : ∀ m, m < r → ¬(0 < m ∧ m ≤ schedule.length ∧
        (schedule.take m).count Side.first =
          (schedule.take m).count Side.second) := by
      intro m hm
      exact Nat.find_min hex hm
    left
    refine ⟨schedule.take r, schedule.drop r,
      (List.take_append_drop r schedule).symm,
      ?_, hr.2.2, ?_⟩
    · apply List.ne_nil_of_length_pos
      rw [List.length_take_of_le hr.2.1]
      exact hr.1
    · intro left right hsplit hleft hright
      have hprefixLength : (schedule.take r).length = r :=
        List.length_take_of_le hr.2.1
      have hleftPos := List.length_pos_of_ne_nil hleft
      have hrightPos := List.length_pos_of_ne_nil hright
      have hleftLt : left.length < r := by
        have := congrArg List.length hsplit
        simp only [List.length_append] at this
        omega
      have htake : schedule.take left.length = left := by
        calc
          schedule.take left.length =
              (schedule.take r).take left.length := by
                rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hleftLt)]
          _ = left := by rw [hsplit]; simp
      apply second_count_gt_first_count left
      · have hheadTake :
            (schedule.take left.length).head? = schedule.head? := by
          cases schedule with
          | nil => simp at hstarts
          | cons side tail =>
              cases left with
              | nil => simp at hleft
              | cons prefixHead prefixTail => simp
        rw [htake] at hheadTake
        rw [hheadTake]
        exact hstarts
      · intro before after hbefore hbeforeNe
        have hbeforePrefix : before <+: left := ⟨after, hbefore.symm⟩
        have hbeforePos := List.length_pos_of_ne_nil hbeforeNe
        have hbeforeLe : before.length ≤ left.length := hbeforePrefix.length_le
        have htakeBefore : schedule.take before.length = before := by
          calc
            schedule.take before.length =
                left.take before.length := by
                  rw [← htake, List.take_take,
                    Nat.min_eq_left hbeforeLe]
            _ = before := by rw [hbefore]; simp
        intro hbalanced
        exact hrMinimal before.length (lt_of_le_of_lt hbeforeLe hleftLt)
          ⟨hbeforePos, hbeforeLe.trans (Nat.le_trans
            (Nat.le_of_lt hleftLt) hr.2.1), by simpa [htakeBefore]⟩
  · right
    intro left right hsplit hleft
    apply second_count_gt_first_count left
    · have hscheduleHead : left.head? = schedule.head? := by
        subst schedule
        cases left with
        | nil => exact (hleft rfl).elim
        | cons side tail => simp
      simpa [hscheduleHead] using hstarts
    · intro before after hbefore hbeforeNe
      have hbeforePrefix : before <+: left := ⟨after, hbefore.symm⟩
      have hleftPrefix : left <+: schedule := ⟨right, hsplit.symm⟩
      have hbeforePrefixSchedule := hbeforePrefix.trans hleftPrefix
      intro hbalanced
      apply hex
      refine ⟨before.length, List.length_pos_of_ne_nil hbeforeNe,
        hbeforePrefixSchedule.length_le, ?_⟩
      have htake : schedule.take before.length = before := by
        rcases hbeforePrefixSchedule with ⟨rest, hrest⟩
        rw [← hrest]
        simp
      simpa [htake] using hbalanced


end D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder

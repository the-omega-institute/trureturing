/- GID: D5/S1/Words/Complexity/LyndonShuffleScheduleOrder
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/LyndonShuffleScheduleOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary fixed-source schedules admit an order-increasing front promotion. -/

import D5.S1.Words.Complexity.LyndonStandardBracket

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Fixed-source order for Lyndon shuffle schedules

A schedule entry names a source-factor index.  Its occurrence number is the
number of earlier entries with the same index.  Thus equal factor words still
have distinct occurrence sources, and every source keeps its original internal
order.
-/
namespace D5.S1.Words.Complexity.LyndonShuffleScheduleOrder

open D5.S1.Words.Complexity.LyndonStandardBracket

variable {A : Type*}

/-- The two fixed sources used by a binary schedule. -/
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

def readTwo (first second : List A) : Side × Nat → Option A
  | (Side.first, i) => first[i]?
  | (Side.second, i) => second[i]?

/-- Evaluate a binary schedule from its two unchanged source words. -/
def evaluateTwo (first second : List A) (schedule : List Side) :
    Option (List A) :=
  (annotateTwo schedule).mapM (readTwo first second)

/-- A binary schedule consumes each fixed source exactly once. -/
def ValidTwoSchedule (first second : List A)
    (schedule : List Side) : Prop :=
  schedule.count Side.first = first.length ∧
    schedule.count Side.second = second.length

private theorem second_occurrence_split (schedule : List Side) (d : Nat)
    (hd : d < schedule.count Side.second) :
    ∃ before after,
      schedule = before ++ Side.second :: after ∧
      before.count Side.second = d := by
  induction schedule generalizing d with
  | nil => simp at hd
  | cons side schedule ih =>
      cases side with
      | first =>
          simp at hd
          rcases ih d hd with ⟨before, after, hsplit, hcount⟩
          exact ⟨Side.first :: before, after, by simp [hsplit], by simp [hcount]⟩
      | second =>
          cases d with
          | zero => exact ⟨[], schedule, by simp, by simp⟩
          | succ d =>
              simp only [List.count_cons, beq_self_eq_true, if_true] at hd
              have htail : d < schedule.count Side.second := by omega
              rcases ih d htail with ⟨before, after, hsplit, hcount⟩
              exact ⟨Side.second :: before, after, by simp [hsplit],
                by simp [hcount]⟩

private theorem evaluateTwo_exists (first second : List A)
    (schedule : List Side)
    (hvalid : ValidTwoSchedule first second schedule) :
    ∃ word, evaluateTwo first second schedule = some word := by
  have hread : ∀ entry ∈ annotateTwo schedule,
      ∃ a, readTwo first second entry = some a := by
    rintro ⟨side, i⟩ hmem
    cases side with
    | first =>
        have hi := first_index_lt_count hmem
        rw [Nat.zero_add, hvalid.1] at hi
        exact ⟨first[i], by
          simp only [readTwo]
          exact List.getElem?_eq_getElem hi⟩
    | second =>
        have hi := second_index_lt_count hmem
        rw [Nat.zero_add, hvalid.2] at hi
        exact ⟨second[i], by
          simp only [readTwo]
          exact List.getElem?_eq_getElem hi⟩
  have mapExists : ∀ entries : List (Side × Nat),
      (∀ entry ∈ entries, ∃ a, readTwo first second entry = some a) →
      ∃ word, entries.mapM (readTwo first second) = some word := by
    intro entries hall
    induction entries with
    | nil => exact ⟨[], rfl⟩
    | cons entry entries ih =>
        rcases hall entry (by simp) with ⟨a, ha⟩
        rcases ih (by
          intro x hx
          exact hall x (by simp [hx])) with ⟨word, hword⟩
        exact ⟨a :: word, by simp [ha, hword]⟩
  simpa [evaluateTwo] using mapExists (annotateTwo schedule) hread

private theorem readTwo_lt_at_first_difference [LinearOrder A]
    (first second : List A) (d : Nat) (firstValue secondValue : A)
    (horder : first ≥ second)
    (hfirst : first[d]? = some firstValue)
    (hsecond : second[d]? = some secondValue)
    (hdiff : firstValue ≠ secondValue)
    (hbefore : ∀ i, i < d → first[i]? = second[i]?) :
    secondValue < firstValue := by
  induction d generalizing first second with
  | zero =>
      cases first with
      | nil => simp at hfirst
      | cons a first =>
          cases second with
          | nil => simp at hsecond
          | cons b second =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hfirst hsecond
              subst a
              subst b
              have hne : secondValue :: second ≠ firstValue :: first := by
                intro heq
                exact hdiff (List.cons.inj heq).1.symm
              have hlt : secondValue :: second < firstValue :: first :=
                lt_of_le_of_ne horder hne
              exact lt_of_le_of_ne (List.head_le_of_lt hlt) hdiff.symm
  | succ d ih =>
      cases first with
      | nil => simp at hfirst
      | cons a first =>
          cases second with
          | nil => simp at hsecond
          | cons b second =>
              have hab : a = b := by
                have := hbefore 0 (by omega)
                simpa using this
              subst b
              have htailOrder : second ≤ first := by
                rcases horder.eq_or_lt with heq | hlt
                · exact (List.cons.inj heq).2.le
                · exact le_of_lt (List.lex_cons_iff.mp hlt)
              apply ih first second
              · exact htailOrder
              · simpa using hfirst
              · simpa using hsecond
              · intro i hi
                have := hbefore (i + 1) (by omega)
                simpa [Nat.add_comm] using this

private theorem option_mapM_congr_on {B C : Type*} (entries : List B)
    (f g : B → Option C) (h : ∀ entry ∈ entries, f entry = g entry) :
    entries.mapM f = entries.mapM g := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rw [List.mapM_cons, List.mapM_cons, h entry (by simp)]
      cases g entry with
      | none => rfl
      | some value =>
          rw [ih (by
            intro x hx
            exact h x (by simp [hx]))]

private theorem option_mapM_lt_of_distinct_prefixes [LinearOrder A]
    {B : Type*} (oldBefore newBefore : List B)
    (oldPivot newPivot : B) (oldAfter newAfter : List B)
    (read : B → Option A) (oldWord newWord common : List A)
    (oldValue newValue : A)
    (holdBefore : oldBefore.mapM read = some common)
    (hnewBefore : newBefore.mapM read = some common)
    (holdPivot : read oldPivot = some oldValue)
    (hnewPivot : read newPivot = some newValue)
    (hpivot : oldValue < newValue)
    (hold : (oldBefore ++ oldPivot :: oldAfter).mapM read = some oldWord)
    (hnew : (newBefore ++ newPivot :: newAfter).mapM read = some newWord) :
    oldWord < newWord := by
  rw [List.mapM_append, holdBefore] at hold
  cases holdAfter : oldAfter.mapM read with
  | none => simp [holdPivot, holdAfter] at hold
  | some oldTail =>
      simp [holdPivot, holdAfter] at hold
      rw [List.mapM_append, hnewBefore] at hnew
      cases hnewAfter : newAfter.mapM read with
      | none => simp [hnewPivot, hnewAfter] at hnew
      | some newTail =>
          simp [hnewPivot, hnewAfter] at hnew
          subst oldWord
          subst newWord
          exact List.Lex.append_left (fun x y : A => x < y)
            (List.Lex.rel hpivot) common

private theorem exists_difference_before_of_length_lt_of_ge [LinearOrder A]
    (first second : List A) (hlen : first.length < second.length)
    (horder : first ≥ second) :
    ∃ d, d < first.length ∧ first[d]? ≠ second[d]? := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => simp at hlen
      | cons b second =>
          exact (not_lt_of_ge horder List.Lex.nil).elim
  | cons a first ih =>
      cases second with
      | nil => simp at hlen
      | cons b second =>
          by_cases hab : a = b
          · subst b
            have htailOrder : second ≤ first := by
              rcases horder.eq_or_lt with heq | hlt
              · exact (List.cons.inj heq).2.le
              · exact le_of_lt (List.lex_cons_iff.mp hlt)
            rcases ih second (by simpa using hlen) htailOrder with
              ⟨d, hd, hdiff⟩
            exact ⟨d + 1, by simp; omega, by simpa [Nat.add_comm] using hdiff⟩
          · exact ⟨0, by simp, by simpa using hab⟩

private theorem swapped_prefix_strict [LinearOrder A]
    (first second : List A) (lead oldTail newTail : List Side)
    (oldWord newWord : List A)
    (horder : first ≥ second)
    (holdValid : ValidTwoSchedule first second (lead ++ oldTail))
    (hnewValid : ValidTwoSchedule first second
      (lead.map swapSide ++ newTail))
    (hold : evaluateTwo first second (lead ++ oldTail) = some oldWord)
    (hnew : evaluateTwo first second (lead.map swapSide ++ newTail) =
      some newWord)
    (hpref : ∀ before after,
      lead = before ++ Side.second :: after →
        before.count Side.first ≤ before.count Side.second)
    (hmismatch : ∃ d, d < lead.count Side.second ∧
      first[d]? ≠ second[d]?) :
    oldWord < newWord := by
  classical
  have hswapFirst :
      ((fun side : Side => side == Side.first) ∘ swapSide) =
        (fun side => side == Side.second) := by
    funext side
    cases side <;> rfl
  have hswapSecond :
      ((fun side : Side => side == Side.second) ∘ swapSide) =
        (fun side => side == Side.first) := by
    funext side
    cases side <;> rfl
  let d := Nat.find hmismatch
  have hd := Nat.find_spec hmismatch
  rcases second_occurrence_split lead d hd.1 with
    ⟨before, after, hlead, hsecondCount⟩
  have hfirstCount : before.count Side.first ≤ d := by
    rw [← hsecondCount]
    exact hpref before after hlead
  have hbeforeEq : ∀ i, i < d → first[i]? = second[i]? := by
    intro i hi
    by_contra hne
    have hcandidate : i < lead.count Side.second ∧
        first[i]? ≠ second[i]? := ⟨hi.trans hd.1, hne⟩
    exact (Nat.find_min hmismatch hi) hcandidate
  have hfirstBound : d < first.length := by
    have hleadCount : lead.count Side.second ≤
        (lead.map swapSide ++ newTail).count Side.first := by
      simp [List.count_eq_countP, List.countP_map, hswapFirst]
    exact hd.1.trans_le (hleadCount.trans_eq hnewValid.1)
  have hsecondBound : d < second.length := by
    have hleadCount : lead.count Side.second ≤
        (lead ++ oldTail).count Side.second := by simp
    exact hd.1.trans_le (hleadCount.trans_eq holdValid.2)
  let firstValue := first[d]'hfirstBound
  let secondValue := second[d]'hsecondBound
  have hfirstRead : first[d]? = some firstValue :=
    List.getElem?_eq_getElem hfirstBound
  have hsecondRead : second[d]? = some secondValue :=
    List.getElem?_eq_getElem hsecondBound
  have hvalueNe : firstValue ≠ secondValue := by
    intro heq
    apply hd.2
    change first[d]? = second[d]?
    rw [hfirstRead, hsecondRead, heq]
  have hpivotLt := readTwo_lt_at_first_difference first second d
    firstValue secondValue horder hfirstRead hsecondRead hvalueNe hbeforeEq
  have hentryEq : ∀ entry ∈ annotateTwo before,
      readTwo first second entry =
        readTwo first second (swapOccurrence entry) := by
    rintro ⟨side, i⟩ hmem
    cases side with
    | first =>
        have hi := first_index_lt_count hmem
        rw [Nat.zero_add] at hi
        have hid : i < d := lt_of_lt_of_le hi hfirstCount
        simpa [readTwo, swapOccurrence, swapSide] using hbeforeEq i hid
    | second =>
        have hi := second_index_lt_count hmem
        rw [Nat.zero_add, hsecondCount] at hi
        simpa [readTwo, swapOccurrence, swapSide] using
          (hbeforeEq i hi).symm
  have hprefixEq :
      (annotateTwo before).mapM (readTwo first second) =
        ((annotateTwo before).map swapOccurrence).mapM
          (readTwo first second) := by
    rw [List.mapM_map]
    exact option_mapM_congr_on (annotateTwo before)
      (readTwo first second)
      (fun entry => readTwo first second (swapOccurrence entry)) hentryEq
  have holdSplit : ∃ rest,
      annotateTwo (lead ++ oldTail) =
        annotateTwo before ++ (Side.second, d) :: rest := by
    subst lead
    refine ⟨annotateTwoFrom (before.count Side.first) (d + 1)
      (after ++ oldTail), ?_⟩
    simp [annotateTwo, annotateTwoFrom_append, hsecondCount,
      annotateTwoFrom]
  have hnewSplit : ∃ rest,
      annotateTwo (lead.map swapSide ++ newTail) =
        (annotateTwo before).map swapOccurrence ++
          (Side.first, d) :: rest := by
    subst lead
    have hsecondCountP :
        before.countP (fun side => side == Side.second) = d := by
      simpa only [List.count_eq_countP] using hsecondCount
    refine ⟨(annotateTwoFrom (before.count Side.first) (d + 1) after).map
        swapOccurrence ++
      annotateTwoFrom (d + 1 + after.count Side.second)
        (before.count Side.first + after.count Side.first) newTail, ?_⟩
    simp [annotateTwo, annotateTwoFrom_append, annotateTwoFrom_swap,
      hsecondCount, annotateTwoFrom, List.count_eq_countP, List.countP_map,
      hswapFirst, hswapSecond, hsecondCountP]
    simp only [swapSide, annotateTwoFrom]
    rw [annotateTwoFrom_append, annotateTwoFrom_swap]
    simp [List.count_eq_countP, List.countP_map,
      hswapFirst, hswapSecond]
  rcases holdSplit with ⟨oldRest, holdSplit⟩
  rcases hnewSplit with ⟨newRest, hnewSplit⟩
  unfold evaluateTwo at hold hnew
  rw [holdSplit] at hold
  rw [hnewSplit] at hnew
  cases hprefix : (annotateTwo before).mapM (readTwo first second) with
  | none =>
      rw [List.mapM_append, hprefix] at hold
      simp at hold
  | some common =>
      have hnewPrefix :
          ((annotateTwo before).map swapOccurrence).mapM
              (readTwo first second) = some common := by
        rw [← hprefixEq]
        exact hprefix
      exact option_mapM_lt_of_distinct_prefixes
        (annotateTwo before) ((annotateTwo before).map swapOccurrence)
        (Side.second, d) (Side.first, d) oldRest newRest
        (readTwo first second) oldWord newWord common secondValue firstValue
        hprefix hnewPrefix (by simpa [readTwo] using hsecondRead)
        (by simpa [readTwo] using hfirstRead) hpivotLt hold hnew

private theorem swapped_balanced_prefix_equal (first second : List A)
    (lead tail : List Side)
    (hbalanced : lead.count Side.first = lead.count Side.second)
    (hequal : ∀ i, i < lead.count Side.first → first[i]? = second[i]?) :
    evaluateTwo first second (lead ++ tail) =
      evaluateTwo first second (lead.map swapSide ++ tail) := by
  have hswapFirst :
      ((fun side : Side => side == Side.first) ∘ swapSide) =
        (fun side => side == Side.second) := by
    funext side
    cases side <;> rfl
  have hswapSecond :
      ((fun side : Side => side == Side.second) ∘ swapSide) =
        (fun side => side == Side.first) := by
    funext side
    cases side <;> rfl
  have hbalancedP :
      lead.countP (fun side => side == Side.first) =
        lead.countP (fun side => side == Side.second) := by
    simpa only [List.count_eq_countP] using hbalanced
  have hentry : ∀ entry ∈ annotateTwo lead,
      readTwo first second entry =
        readTwo first second (swapOccurrence entry) := by
    rintro ⟨side, i⟩ hmem
    cases side with
    | first =>
        have hi := first_index_lt_count hmem
        rw [Nat.zero_add] at hi
        simpa [readTwo, swapOccurrence, swapSide] using hequal i hi
    | second =>
        have hi := second_index_lt_count hmem
        rw [Nat.zero_add, ← hbalanced] at hi
        simpa [readTwo, swapOccurrence, swapSide] using (hequal i hi).symm
  have hprefix :
      (annotateTwo lead).mapM (readTwo first second) =
        ((annotateTwo lead).map swapOccurrence).mapM
          (readTwo first second) := by
    rw [List.mapM_map]
    exact option_mapM_congr_on (annotateTwo lead)
      (readTwo first second)
      (fun entry => readTwo first second (swapOccurrence entry)) hentry
  unfold evaluateTwo annotateTwo
  rw [annotateTwoFrom_append, annotateTwoFrom_append,
    annotateTwoFrom_swap]
  simp only [List.count_eq_countP, List.countP_map,
    hswapFirst, hswapSecond, hbalancedP]
  have hprefix' :
      (annotateTwoFrom 0 0 lead).mapM (readTwo first second) =
        ((annotateTwoFrom 0 0 lead).map swapOccurrence).mapM
          (readTwo first second) := by
    simpa [annotateTwo] using hprefix
  rw [List.mapM_append, List.mapM_append, hprefix']

/-- A binary schedule beginning at the smaller source can be promoted to begin
at the larger source without changing either source word or decreasing its
evaluation. -/
theorem fixedSource_frontPromotion [LinearOrder A]
    (first second : List A) (schedule : List Side) (word : List A)
    (horder : first ≥ second)
    (hvalid : ValidTwoSchedule first second schedule)
    (hstarts : schedule.head? = some Side.second)
    (heval : evaluateTwo first second schedule = some word) :
    ∃ promoted promotedWord,
      ValidTwoSchedule first second promoted ∧
      promoted.head? = some Side.first ∧
      evaluateTwo first second promoted = some promotedWord ∧
      word ≤ promotedWord := by
  classical
  have hswapFirst :
      ((fun side : Side => side == Side.first) ∘ swapSide) =
        (fun side => side == Side.second) := by
    funext side
    cases side <;> rfl
  have hswapSecond :
      ((fun side : Side => side == Side.second) ∘ swapSide) =
        (fun side => side == Side.first) := by
    funext side
    cases side <;> rfl
  rcases first_return_or_always_ahead schedule hstarts with hreturn | hahead
  · rcases hreturn with
      ⟨lead, tail, hschedule, hleadNe, hbalanced, hproper⟩
    rw [hschedule] at hvalid heval hstarts
    let promoted := lead.map swapSide ++ tail
    have hpvalid : ValidTwoSchedule first second promoted := by
      dsimp [promoted]
      have hbalancedP :
          lead.countP (fun side => side == Side.first) =
            lead.countP (fun side => side == Side.second) := by
        simpa only [List.count_eq_countP] using hbalanced
      constructor
      · have hold := hvalid.1
        simp only [List.count_append] at hold ⊢
        simp only [List.count_eq_countP, List.countP_map,
          hswapFirst]
        rw [← hbalancedP]
        simpa only [List.count_eq_countP] using hold
      · have hold := hvalid.2
        simp only [List.count_append] at hold ⊢
        simp only [List.count_eq_countP, List.countP_map,
          hswapSecond]
        rw [hbalancedP]
        simpa only [List.count_eq_countP] using hold
    have hphead : promoted.head? = some Side.first := by
      cases lead with
      | nil => exact (hleadNe rfl).elim
      | cons side lead =>
          simp only [List.cons_append, List.head?_cons] at hstarts
          have hside : side = Side.second := Option.some.inj hstarts
          subst side
          simp [promoted, swapSide]
    rcases evaluateTwo_exists first second promoted hpvalid with
      ⟨promotedWord, hpromoted⟩
    refine ⟨promoted, promotedWord, hpvalid, hphead, hpromoted, ?_⟩
    by_cases hmismatch : ∃ d, d < lead.count Side.second ∧
        first[d]? ≠ second[d]?
    · apply le_of_lt
      apply swapped_prefix_strict first second lead tail tail word promotedWord
        horder hvalid hpvalid heval hpromoted
      · intro before after hsplit
        by_cases hbefore : before = []
        · simp [hbefore]
        · exact (hproper before (Side.second :: after) (by simpa using hsplit)
            hbefore (by simp)).le
      · exact hmismatch
    · have hequal : ∀ i, i < lead.count Side.first →
          first[i]? = second[i]? := by
        intro i hi
        by_contra hne
        exact hmismatch ⟨i, by simpa [hbalanced] using hi, hne⟩
      have hevalEq := swapped_balanced_prefix_equal first second lead tail
        hbalanced hequal
      rw [heval, hpromoted] at hevalEq
      exact Option.some.inj hevalEq |>.le
  · have hcountLt := second_count_gt_first_count schedule hstarts (by
      intro left right hsplit hleft heq
      exact (Nat.ne_of_lt (hahead left right hsplit hleft)) heq)
    have hlengthLt : first.length < second.length := by
      simpa [hvalid.1, hvalid.2] using hcountLt
    have hfirstPos : 0 < first.length := by
      cases first with
      | nil =>
          cases second with
          | nil => simp at hlengthLt
          | cons b second => exact (not_lt_of_ge horder List.Lex.nil).elim
      | cons a first => simp
    let cut := first.length - 1
    have hcut : cut < schedule.count Side.second := by
      rw [hvalid.2]
      dsimp [cut]
      omega
    rcases second_occurrence_split schedule cut hcut with
      ⟨before, oldTail, hschedule, hbeforeCount⟩
    let lead := before ++ [Side.second]
    have hleadSecond : lead.count Side.second = first.length := by
      simp [lead, hbeforeCount, cut]
      omega
    have hleadNe : lead ≠ [] := by simp [lead]
    have hleadFirstLt : lead.count Side.first < first.length := by
      have := hahead lead oldTail (by simpa [lead] using hschedule) hleadNe
      simpa [hleadSecond] using this
    let promoted := lead.map swapSide ++
      List.replicate (second.length - lead.count Side.first) Side.second
    have hrepFirst :
        (List.replicate (second.length - lead.count Side.first) Side.second).count
          Side.first = 0 := by
      induction second.length - lead.count Side.first with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, ih]
    have hpvalid : ValidTwoSchedule first second promoted := by
      dsimp [promoted]
      constructor
      · rw [List.count_append, show
            (lead.map swapSide).count Side.first = lead.count Side.second by
          rw [List.count_eq_countP, List.countP_map, hswapFirst,
            ← List.count_eq_countP]]
        simp [hleadSecond, hrepFirst]
      · rw [List.count_append, show
            (lead.map swapSide).count Side.second = lead.count Side.first by
          rw [List.count_eq_countP, List.countP_map, hswapSecond,
            ← List.count_eq_countP]]
        simp
        omega
    have hphead : promoted.head? = some Side.first := by
      rw [hschedule] at hstarts
      cases before with
      | nil => simp [lead, promoted, swapSide]
      | cons side before =>
          have hside : side = Side.second := by simpa using hstarts
          subst side
          simp [lead, promoted, swapSide]
    rcases evaluateTwo_exists first second promoted hpvalid with
      ⟨promotedWord, hpromoted⟩
    refine ⟨promoted, promotedWord, hpvalid, hphead, hpromoted, ?_⟩
    apply le_of_lt
    rw [hschedule] at hvalid heval
    have holdValid : ValidTwoSchedule first second (lead ++ oldTail) := by
      simpa [lead] using hvalid
    have holdEval : evaluateTwo first second (lead ++ oldTail) = some word := by
      simpa [lead] using heval
    have hpref : ∀ pre rest,
        lead = pre ++ Side.second :: rest →
          pre.count Side.first ≤ pre.count Side.second := by
      intro pre rest hsplit
      by_cases hprefix : pre = []
      · simp [hprefix]
      · exact (hahead pre (Side.second :: rest ++ oldTail)
          (by
            rw [hschedule]
            calc
              before ++ Side.second :: oldTail = lead ++ oldTail := by
                simp [lead]
              _ = (pre ++ Side.second :: rest) ++ oldTail := by rw [hsplit]
              _ = pre ++ (Side.second :: rest ++ oldTail) := by simp)
          hprefix).le
    have hmismatch : ∃ d, d < lead.count Side.second ∧
        first[d]? ≠ second[d]? := by
      rcases exists_difference_before_of_length_lt_of_ge first second
          hlengthLt horder with ⟨d, hd, hdiff⟩
      exact ⟨d, by simpa [hleadSecond] using hd, hdiff⟩
    exact swapped_prefix_strict first second lead oldTail
      (List.replicate (second.length - lead.count Side.first) Side.second)
      word promotedWord horder holdValid hpvalid holdEval hpromoted hpref hmismatch

end D5.S1.Words.Complexity.LyndonShuffleScheduleOrder

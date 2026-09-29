/- GID: D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary schedule evaluation compares swapped fixed-source prefixes. -/

import D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder
import Mathlib.Data.List.Lex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleEvaluation

open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder
open private annotateTwoFrom_append annotateTwoFrom_swap first_index_lt_count
  second_index_lt_count swapOccurrence swapSide from
  D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder

variable {A : Type*}

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


end D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleEvaluation

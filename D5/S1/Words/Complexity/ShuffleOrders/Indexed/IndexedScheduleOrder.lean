/- GID: D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Indexed schedules preserve every occurrence of every fixed source. -/

import D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryFrontPromotion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleOrder

open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder

variable {A : Type*}

abbrev IndexedSchedule := List Nat

/-- A schedule uses every occurrence of every source exactly once and preserves
the internal order of each source. -/
def IsValidSchedule (factors : List (List A))
    (schedule : IndexedSchedule) : Prop :=
  ∀ i, schedule.count i = (factors.getD i []).length

def annotateIndexedFrom (used : Nat → Nat) :
    IndexedSchedule → List (Nat × Nat)
  | [] => []
  | i :: schedule =>
      (i, used i) :: annotateIndexedFrom (Function.update used i (used i + 1)) schedule

def annotateIndexed : IndexedSchedule → List (Nat × Nat) :=
  annotateIndexedFrom (fun _ => 0)

def readIndexed (factors : List (List A)) : Nat × Nat → Option A
  | (i, occurrence) => (factors.getD i [])[occurrence]?

/-- Read a schedule from its fixed sources. Invalid indices return `none`. -/
noncomputable def evaluateSchedule (factors : List (List A))
    (schedule : IndexedSchedule) : Option (List A) := by
  classical
  exact if h : IsValidSchedule factors schedule then
      (annotateIndexed schedule).mapM (readIndexed factors)
    else none

private def occurrenceRun (i start : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | count + 1 => (i, start) :: occurrenceRun i (start + 1) count

private def TraceValidFrom (factors : List (List A)) (used : Nat → Nat)
    (trace : List (Nat × Nat)) : Prop :=
  ∀ i, trace.filter (fun entry => entry.1 = i) =
    occurrenceRun i (used i) ((factors.getD i []).length - used i)

private theorem filter_annotateIndexedFrom (used : Nat → Nat)
    (schedule : IndexedSchedule) (i : Nat) :
    (annotateIndexedFrom used schedule).filter (fun entry => entry.1 = i) =
      occurrenceRun i (used i) (schedule.count i) := by
  induction schedule generalizing used with
  | nil => simp [annotateIndexedFrom, occurrenceRun]
  | cons label schedule ih =>
      by_cases hlabel : label = i
      · subst label
        simp [annotateIndexedFrom, List.filter_cons, ih, occurrenceRun]
      · have hilabel : i ≠ label := Ne.symm hlabel
        simp [annotateIndexedFrom, List.filter_cons, ih, occurrenceRun,
          hlabel, hilabel, Function.update]

private theorem trace_read_exists (factors : List (List A))
    (used : Nat → Nat) (trace : List (Nat × Nat))
    (hused : ∀ i, used i ≤ (factors.getD i []).length)
    (hvalid : TraceValidFrom factors used trace) :
    ∃ word, trace.mapM (readIndexed factors) = some word := by
  have hread : ∀ entry ∈ trace, ∃ a, readIndexed factors entry = some a := by
    rintro ⟨i, occurrence⟩ hmem
    have hfiltered : (i, occurrence) ∈
        trace.filter (fun entry => entry.1 = i) := by
      exact List.mem_filter.mpr ⟨hmem, by simp⟩
    rw [hvalid i] at hfiltered
    have occurrenceRun_bound : ∀ count start occurrence,
        (i, occurrence) ∈ occurrenceRun i start count →
          start ≤ occurrence ∧ occurrence < start + count := by
      intro count
      induction count with
      | zero => simp [occurrenceRun]
      | succ count ih =>
          intro start occurrence hmem
          simp only [occurrenceRun, List.mem_cons, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩ | hmem
          · omega
          · have := ih (start + 1) occurrence hmem
            omega
    have hbounds := occurrenceRun_bound
      ((factors.getD i []).length - used i) (used i) occurrence hfiltered
    have hlt : occurrence < (factors.getD i []).length := by
      have := hused i
      omega
    exact ⟨(factors.getD i [])[occurrence], by
      simp only [readIndexed]
      exact List.getElem?_eq_getElem hlt⟩
  have mapExists : ∀ entries : List (Nat × Nat),
      (∀ entry ∈ entries, ∃ a, readIndexed factors entry = some a) →
      ∃ word, entries.mapM (readIndexed factors) = some word := by
    intro entries
    induction entries with
    | nil =>
        intro _
        exact ⟨[], rfl⟩
    | cons entry entries ih =>
        intro hall
        rcases hall entry (by simp) with ⟨a, ha⟩
        rcases ih (by
          intro x hx
          exact hall x (by simp [hx])) with ⟨word, hword⟩
        exact ⟨a :: word, by simp [ha, hword]⟩
  exact mapExists trace hread

private def selectsPair (j : Nat) (entry : Nat × Nat) : Bool :=
  decide (entry.1 = 0 ∨ entry.1 = j + 1)

private def pairSide (entry : Nat × Nat) : Side :=
  if entry.1 = 0 then Side.first else Side.second

private def relabelPair (j : Nat) : Side × Nat → Nat × Nat
  | (Side.first, occurrence) => (0, occurrence)
  | (Side.second, occurrence) => (j + 1, occurrence)

private theorem pair_trace_eq_annotateTwoFrom (j firstStart secondStart : Nat)
    (trace : List (Nat × Nat)) (firstCount secondCount : Nat)
    (hlabels : ∀ entry ∈ trace,
      entry.1 = 0 ∨ entry.1 = j + 1)
    (hfirst : trace.filter (fun entry => entry.1 = 0) =
      occurrenceRun 0 firstStart firstCount)
    (hsecond : trace.filter (fun entry => entry.1 = j + 1) =
      occurrenceRun (j + 1) secondStart secondCount) :
    (annotateTwoFrom firstStart secondStart (trace.map pairSide)).map
        (relabelPair j) = trace := by
  induction trace generalizing firstStart secondStart firstCount secondCount with
  | nil => simp [annotateTwoFrom]
  | cons entry trace ih =>
      rcases entry with ⟨label, occurrence⟩
      have hlabel := hlabels (label, occurrence) (by simp)
      have htailLabels : ∀ entry ∈ trace,
          entry.1 = 0 ∨ entry.1 = j + 1 := by
        intro item hitem
        exact hlabels item (by simp [hitem])
      rcases hlabel with rfl | hlabel
      · cases firstCount with
        | zero => simp [occurrenceRun] at hfirst
        | succ firstCount =>
            have hoccurrence : occurrence = firstStart := by
              simpa [occurrenceRun] using congrArg List.head? hfirst
            subst occurrence
            have htailFirst :
                trace.filter (fun entry => entry.1 = 0) =
                  occurrenceRun 0 (firstStart + 1) firstCount := by
              simpa [occurrenceRun] using congrArg List.tail hfirst
            have htailSecond :
                trace.filter (fun entry => entry.1 = j + 1) =
                  occurrenceRun (j + 1) secondStart secondCount := by
              simpa using hsecond
            simp only [List.map_cons, pairSide, if_pos, annotateTwoFrom,
              relabelPair]
            rw [ih (firstStart := firstStart + 1)
              (secondStart := secondStart) (firstCount := firstCount)
              (secondCount := secondCount) htailLabels htailFirst htailSecond]
      · change label = j + 1 at hlabel
        subst label
        have hj : j + 1 ≠ 0 := by omega
        cases secondCount with
        | zero => simp [occurrenceRun, hj] at hsecond
        | succ secondCount =>
            have hoccurrence : occurrence = secondStart := by
              simpa [occurrenceRun, hj] using congrArg List.head? hsecond
            subst occurrence
            have htailFirst :
                trace.filter (fun entry => entry.1 = 0) =
                  occurrenceRun 0 firstStart firstCount := by
              simpa [hj] using hfirst
            have htailSecond :
                trace.filter (fun entry => entry.1 = j + 1) =
                  occurrenceRun (j + 1) (secondStart + 1) secondCount := by
              simpa [occurrenceRun] using congrArg List.tail hsecond
            simp only [List.map_cons, pairSide, if_neg hj, annotateTwoFrom,
              relabelPair]
            rw [ih (firstStart := firstStart)
              (secondStart := secondStart + 1) (firstCount := firstCount)
              (secondCount := secondCount) htailLabels htailFirst htailSecond]

private theorem occurrenceRun_length (i start count : Nat) :
    (occurrenceRun i start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [occurrenceRun, ih]

private theorem filter_relabel_annotate_first (j firstStart secondStart : Nat)
    (schedule : List Side) :
    ((annotateTwoFrom firstStart secondStart schedule).map
        (relabelPair j)).filter (fun entry => entry.1 = 0) =
      occurrenceRun 0 firstStart (schedule.count Side.first) := by
  induction schedule generalizing firstStart secondStart with
  | nil => rfl
  | cons side schedule ih =>
      cases side with
      | first => simp [annotateTwoFrom, relabelPair, occurrenceRun, ih]
      | second =>
          have hj : j + 1 ≠ 0 := by omega
          simp [annotateTwoFrom, relabelPair, occurrenceRun, hj, ih]

private theorem filter_relabel_annotate_second (j firstStart secondStart : Nat)
    (schedule : List Side) :
    ((annotateTwoFrom firstStart secondStart schedule).map
        (relabelPair j)).filter (fun entry => entry.1 = j + 1) =
      occurrenceRun (j + 1) secondStart (schedule.count Side.second) := by
  induction schedule generalizing firstStart secondStart with
  | nil => rfl
  | cons side schedule ih =>
      cases side with
      | first =>
          have hj : 0 ≠ j + 1 := by omega
          simp [annotateTwoFrom, relabelPair, occurrenceRun, hj, ih]
      | second => simp [annotateTwoFrom, relabelPair, occurrenceRun, ih]

private theorem mapM_filter_exists {B : Type*} (entries : List B)
    (selected : B → Bool) (read : B → Option A) (word : List A)
    (hread : entries.mapM read = some word) :
    ∃ selectedWord,
      (entries.filter selected).mapM read = some selectedWord := by
  induction entries generalizing word with
  | nil => exact ⟨[], rfl⟩
  | cons entry entries ih =>
      cases hentry : read entry with
      | none => simp [hentry] at hread
      | some value =>
          cases htail : entries.mapM read with
          | none => simp [hentry, htail] at hread
          | some tail =>
              rcases ih tail htail with ⟨selectedWord, hselected⟩
              cases hchoice : selected entry with
              | false => exact ⟨selectedWord, by simp [hchoice, hselected]⟩
              | true => exact ⟨value :: selectedWord,
                  by simp [hchoice, hentry, hselected]⟩


end D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleOrder

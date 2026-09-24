/- GID: D5/S1/Words/Complexity/LyndonIndexedShuffleOrder
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/LyndonIndexedShuffleOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Indexed Lyndon schedules are bounded by ordered factor concatenation. -/

import D5.S1.Words.Complexity.LyndonShuffleScheduleOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Indexed fixed-source order for Lyndon shuffle schedules

An indexed schedule distinguishes factor occurrences even when two factor words
are equal.  Binary front promotion is lifted to selected source pairs and then
iterated through the leading Lyndon factor.
-/
namespace D5.S1.Words.Complexity.LyndonIndexedShuffleOrder

open D5.S1.Words.Complexity.LyndonStandardBracket
open D5.S1.Words.Complexity.LyndonShuffleScheduleOrder

variable {A : Type*}

/-- A factor-index schedule. Repeated indices denote successive occurrences
from the same fixed source. -/
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

private def weave : List Bool → List A → List A → List A
  | [], _, _ => []
  | true :: mask, selected, other =>
      match selected with
      | [] => []
      | value :: selected => value :: weave mask selected other
  | false :: mask, selected, other =>
      match other with
      | [] => []
      | value :: other => value :: weave mask selected other

private theorem weave_le [LinearOrder A] (mask : List Bool)
    (oldSelected newSelected other : List A)
    (holdLength : oldSelected.length = mask.count true)
    (hnewLength : newSelected.length = mask.count true)
    (hotherLength : other.length = mask.count false)
    (hselected : oldSelected ≤ newSelected) :
    weave mask oldSelected other ≤ weave mask newSelected other := by
  induction mask generalizing oldSelected newSelected other with
  | nil => simp [weave]
  | cons selected mask ih =>
      cases selected with
      | false =>
          cases other with
          | nil => simp at hotherLength
          | cons value other =>
              simp at holdLength hnewLength hotherLength
              simp only [weave]
              exact List.cons_le_cons value
                (ih oldSelected newSelected other holdLength hnewLength
                  (by omega) hselected)
      | true =>
          cases oldSelected with
          | nil => simp at holdLength
          | cons oldValue oldSelected =>
              cases newSelected with
              | nil => simp at hnewLength
              | cons newValue newSelected =>
                  simp at holdLength hnewLength hotherLength
                  simp only [weave]
                  rcases hselected.eq_or_lt with heq | hlt
                  · cases heq
                    exact le_rfl
                  · cases hlt with
                    | rel hvalue => exact le_of_lt (List.Lex.rel hvalue)
                    | cons htail =>
                        exact List.cons_le_cons oldValue
                          (ih oldSelected newSelected other (by omega) (by omega)
                            hotherLength (le_of_lt htail))

private theorem mapM_eq_weave {B : Type*} (entries : List B)
    (selected : B → Bool) (read : B → Option A)
    (word selectedWord otherWord : List A)
    (hword : entries.mapM read = some word)
    (hselected : (entries.filter selected).mapM read = some selectedWord)
    (hother : (entries.filter fun entry => !selected entry).mapM read =
      some otherWord) :
    word = weave (entries.map selected) selectedWord otherWord := by
  induction entries generalizing word selectedWord otherWord with
  | nil =>
      simp at hword hselected hother
      subst word
      subst selectedWord
      subst otherWord
      rfl
  | cons entry entries ih =>
      cases hread : read entry with
      | none => simp [hread] at hword
      | some value =>
          cases htail : entries.mapM read with
          | none => simp [hread, htail] at hword
          | some tail =>
              simp [hread, htail] at hword
              subst word
              cases hchoice : selected entry with
              | false =>
                  have hselectedTail :
                      (entries.filter selected).mapM read = some selectedWord := by
                    simpa [hchoice] using hselected
                  cases hotherTail :
                      (entries.filter fun item => !selected item).mapM read with
                  | none => simp [hchoice, hread, hotherTail] at hother
                  | some otherTail =>
                      have hotherWord : otherWord = value :: otherTail := by
                        simpa [hchoice, hread, hotherTail] using hother.symm
                      subst otherWord
                      rw [ih tail selectedWord otherTail htail hselectedTail
                        hotherTail]
                      simp [weave, hchoice]
              | true =>
                  have hotherTail :
                      (entries.filter fun item => !selected item).mapM read =
                        some otherWord := by
                    simpa [hchoice] using hother
                  cases hselectedTail : (entries.filter selected).mapM read with
                  | none => simp [hchoice, hread, hselectedTail] at hselected
                  | some selectedTail =>
                      have hselectedWord :
                          selectedWord = value :: selectedTail := by
                        simpa [hchoice, hread, hselectedTail] using hselected.symm
                      subst selectedWord
                      rw [ih tail selectedTail otherWord htail hselectedTail
                        hotherTail]
                      simp [weave, hchoice]

private def refillWhere {B : Type*} (selected : B → Bool) :
    List B → List B → Option (List B)
  | replacements, [] => if replacements = [] then some [] else none
  | replacements, entry :: entries =>
      if selected entry then
        match replacements with
        | [] => none
        | replacement :: replacements =>
            (replacement :: ·) <$> refillWhere selected replacements entries
      else
        (entry :: ·) <$> refillWhere selected replacements entries

private theorem refillWhere_spec {B : Type*} (selected : B → Bool)
    (replacements entries : List B)
    (hlength : replacements.length = (entries.filter selected).length)
    (hreplacements : ∀ replacement ∈ replacements,
      selected replacement = true) :
    ∃ filled,
      refillWhere selected replacements entries = some filled ∧
      filled.map selected = entries.map selected ∧
      filled.filter selected = replacements ∧
      filled.filter (fun entry => !selected entry) =
        entries.filter (fun entry => !selected entry) := by
  induction entries generalizing replacements with
  | nil =>
      have hreplacementsNil : replacements = [] := by simpa using hlength
      subst replacements
      exact ⟨[], by simp [refillWhere]⟩
  | cons entry entries ih =>
      cases hchoice : selected entry with
      | false =>
          have htailLength :
              replacements.length = (entries.filter selected).length := by
            simpa [hchoice] using hlength
          rcases ih replacements htailLength hreplacements with
            ⟨filled, hfill, hmask, hselected, hother⟩
          refine ⟨entry :: filled, ?_, ?_, ?_, ?_⟩
          · simp [refillWhere, hchoice, hfill]
          · simp [hchoice, hmask]
          · simp [hchoice, hselected]
          · simp [hchoice, hother]
      | true =>
          cases replacements with
          | nil => simp [hchoice] at hlength
          | cons replacement replacements =>
              have hreplacement : selected replacement = true :=
                hreplacements replacement (by simp)
              have htailReplacements : ∀ item ∈ replacements,
                  selected item = true := by
                intro item hitem
                exact hreplacements item (by simp [hitem])
              have htailLength :
                  replacements.length = (entries.filter selected).length := by
                simpa [hchoice] using hlength
              rcases ih replacements htailLength htailReplacements with
                ⟨filled, hfill, hmask, hselected, hother⟩
              refine ⟨replacement :: filled, ?_, ?_, ?_, ?_⟩
              · simp [refillWhere, hchoice, hfill]
              · simp [hchoice, hreplacement, hmask]
              · simp [hreplacement, hselected]
              · simp [hchoice, hreplacement, hother]

theorem mapM_length {B : Type*} (read : B → Option A)
    (entries : List B) (word : List A)
    (hread : entries.mapM read = some word) : word.length = entries.length := by
  induction entries generalizing word with
  | nil =>
      simp at hread
      subst word
      rfl
  | cons entry entries ih =>
      cases hentry : read entry with
      | none => simp [hentry] at hread
      | some value =>
          cases htail : entries.mapM read with
          | none => simp [hentry, htail] at hread
          | some tail =>
              have hword : word = value :: tail := by
                simpa [hentry, htail] using hread.symm
              subst word
              simp [ih tail htail]

private theorem refillWhere_mapM_mono [LinearOrder A] {B : Type*}
    (selected : B → Bool) (read : B → Option A)
    (replacements entries filled : List B)
    (oldWord newWord oldSelected newSelected otherWord : List A)
    (hlength : replacements.length = (entries.filter selected).length)
    (hreplacements : ∀ replacement ∈ replacements,
      selected replacement = true)
    (hfill : refillWhere selected replacements entries = some filled)
    (hold : entries.mapM read = some oldWord)
    (hnew : filled.mapM read = some newWord)
    (holdSelected : (entries.filter selected).mapM read = some oldSelected)
    (hnewSelected : replacements.mapM read = some newSelected)
    (hother : (entries.filter fun entry => !selected entry).mapM read =
      some otherWord)
    (hselected : oldSelected ≤ newSelected) : oldWord ≤ newWord := by
  rcases refillWhere_spec selected replacements entries hlength hreplacements with
    ⟨expected, hexpected, hmask, hselectedFilter, hotherFilter⟩
  rw [hfill] at hexpected
  cases Option.some.inj hexpected
  have hnewSelected' :
      (filled.filter selected).mapM read = some newSelected := by
    rw [hselectedFilter]
    exact hnewSelected
  have hnewOther :
      (filled.filter fun entry => !selected entry).mapM read = some otherWord := by
    rw [hotherFilter]
    exact hother
  have holdWeave := mapM_eq_weave entries selected read oldWord oldSelected
    otherWord hold holdSelected hother
  have hnewWeave := mapM_eq_weave filled selected read newWord newSelected
    otherWord hnew hnewSelected' hnewOther
  rw [hmask] at hnewWeave
  rw [holdWeave, hnewWeave]
  have hselectedTrue :
      ((fun choice : Bool => choice == true) ∘ selected) = selected := by
    funext entry
    cases hchoice : selected entry <;> simp [Function.comp_def, hchoice]
  have hselectedFalse :
      ((fun choice : Bool => choice == false) ∘ selected) =
        (fun entry => !selected entry) := by
    funext entry
    cases hchoice : selected entry <;> simp [Function.comp_def, hchoice]
  apply weave_le (entries.map selected) oldSelected newSelected otherWord
  · rw [mapM_length read _ _ holdSelected,
      List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
      hselectedTrue]
  · rw [mapM_length read _ _ hnewSelected, hlength,
      List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
      hselectedTrue]
  · rw [mapM_length read _ _ hother,
      List.count_eq_countP, List.countP_map, List.countP_eq_length_filter,
      hselectedFalse]
  · exact hselected

private theorem annotateTwoFrom_length (firstStart secondStart : Nat)
    (schedule : List Side) :
    (annotateTwoFrom firstStart secondStart schedule).length = schedule.length := by
  induction schedule generalizing firstStart secondStart with
  | nil => rfl
  | cons side schedule ih => cases side <;> simp [annotateTwoFrom, ih]

private theorem promote_trace_front [LinearOrder A]
    (u : List A) (tail : List (List A)) (t j : Nat)
    (trace : List (Nat × Nat)) (word : List A)
    (ht : t ≤ u.length)
    (hvalid : TraceValidFrom (u :: tail)
      (fun i => if i = 0 then t else 0) trace)
    (hhead : trace.head? = some (j + 1, 0))
    (horder : u.drop t ≥ tail.getD j [])
    (heval : trace.mapM (readIndexed (u :: tail)) = some word) :
    ∃ promoted promotedWord,
      TraceValidFrom (u :: tail) (fun i => if i = 0 then t else 0)
        promoted ∧
      promoted.head? = some (0, t) ∧
      promoted.mapM (readIndexed (u :: tail)) = some promotedWord ∧
      word ≤ promotedWord := by
  classical
  have filterSelectedZero (trace : List (Nat × Nat)) :
      (trace.filter (selectsPair j)).filter (fun entry => entry.1 = 0) =
        trace.filter (fun entry => entry.1 = 0) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro entry _
    by_cases h0 : entry.1 = 0 <;> simp [selectsPair, h0]
  have filterSelectedSecond (trace : List (Nat × Nat)) :
      (trace.filter (selectsPair j)).filter
          (fun entry => entry.1 = j + 1) =
        trace.filter (fun entry => entry.1 = j + 1) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro entry _
    by_cases hj : entry.1 = j + 1 <;> simp [selectsPair, hj]
  have filterUnselectedOther (i : Nat) (hi0 : i ≠ 0)
      (hij : i ≠ j + 1) (trace : List (Nat × Nat)) :
      (trace.filter (fun entry => !selectsPair j entry)).filter
          (fun entry => entry.1 = i) =
        trace.filter (fun entry => entry.1 = i) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro entry _
    by_cases hi : entry.1 = i
    · subst i
      simp [selectsPair, hi0, hij]
    · simp [selectsPair, hi]
  have readPair (binary : List Side) :
      ((annotateTwoFrom t 0 binary).map (relabelPair j)).mapM
          (readIndexed (u :: tail)) =
        evaluateTwo (u.drop t) (tail.getD j []) binary := by
    have hshift : annotateTwoFrom t 0 binary =
        (annotateTwo binary).map (shiftPairOccurrences t 0) := by
      simpa [annotateTwo] using annotateTwoFrom_add t 0 binary 0 0
    rw [hshift, List.map_map, List.mapM_map]
    unfold evaluateTwo
    congr 1
    funext entry
    rcases entry with ⟨side, occurrence⟩
    cases side with
    | first => simp [Function.comp_def, readIndexed, readTwo, relabelPair,
        shiftPairOccurrences, List.getElem?_drop, Nat.add_comm]
    | second => simp [Function.comp_def, readIndexed, readTwo, relabelPair,
        shiftPairOccurrences]
  cases trace with
  | nil => simp at hhead
  | cons entry rest =>
      have hentry : entry = (j + 1, 0) := by simpa using hhead
      subst entry
      let trace := (j + 1, 0) :: rest
      let selectedTrace := trace.filter (selectsPair j)
      let schedule := selectedTrace.map pairSide
      have hlabels : ∀ entry ∈ selectedTrace,
          entry.1 = 0 ∨ entry.1 = j + 1 := by
        intro selected hselected
        have hpick := (List.mem_filter.mp hselected).2
        simpa [selectedTrace, selectsPair] using hpick
      have hfirst : selectedTrace.filter (fun entry => entry.1 = 0) =
          occurrenceRun 0 t (u.length - t) := by
        have h := hvalid 0
        rw [filterSelectedZero]
        simpa [trace] using h
      have hsecond : selectedTrace.filter (fun entry => entry.1 = j + 1) =
          occurrenceRun (j + 1) 0 (tail.getD j []).length := by
        have h := hvalid (j + 1)
        rw [filterSelectedSecond]
        simpa [trace] using h
      have htrace :
          (annotateTwoFrom t 0 schedule).map (relabelPair j) =
            selectedTrace := by
        exact pair_trace_eq_annotateTwoFrom j t 0 selectedTrace
          (u.length - t) (tail.getD j []).length hlabels hfirst hsecond
      have hscheduleValid :
          ValidTwoSchedule (u.drop t) (tail.getD j []) schedule := by
        constructor
        · rw [List.count_eq_countP, List.countP_map,
            List.countP_eq_length_filter]
          have hfilter :
              selectedTrace.filter
                  ((fun side : Side => side == Side.first) ∘ pairSide) =
                selectedTrace.filter (fun entry => entry.1 = 0) := by
            apply List.filter_congr
            intro entry hentry
            rcases entry with ⟨label, occurrence⟩
            rcases hlabels (label, occurrence) hentry with hlabel | hlabel
            · change label = 0 at hlabel
              subst label
              simp [pairSide]
            · change label = j + 1 at hlabel
              subst label
              have hj : j + 1 ≠ 0 := by omega
              simp [pairSide, hj]
          rw [hfilter, hfirst, occurrenceRun_length]
          simp [ht]
        · rw [List.count_eq_countP, List.countP_map,
            List.countP_eq_length_filter]
          have hfilter :
              selectedTrace.filter
                  ((fun side : Side => side == Side.second) ∘ pairSide) =
                selectedTrace.filter (fun entry => entry.1 = j + 1) := by
            apply List.filter_congr
            intro entry hentry
            rcases entry with ⟨label, occurrence⟩
            rcases hlabels (label, occurrence) hentry with hlabel | hlabel
            · change label = 0 at hlabel
              subst label
              have hj : 0 ≠ j + 1 := by omega
              simp [pairSide, hj]
            · change label = j + 1 at hlabel
              subst label
              have hj : j + 1 ≠ 0 := by omega
              simp [pairSide, hj]
          rw [hfilter, hsecond, occurrenceRun_length]
      have hscheduleHead : schedule.head? = some Side.second := by
        simp [schedule, selectedTrace, trace, selectsPair, pairSide]
      rcases mapM_filter_exists trace (selectsPair j)
          (readIndexed (u :: tail)) word heval with
        ⟨selectedWord, hselectedRead⟩
      have hbinaryEval :
          evaluateTwo (u.drop t) (tail.getD j []) schedule =
            some selectedWord := by
        rw [← readPair schedule, htrace]
        exact hselectedRead
      rcases fixedSource_frontPromotion (u.drop t) (tail.getD j [])
          schedule selectedWord horder hscheduleValid hscheduleHead hbinaryEval with
        ⟨promotedSchedule, promotedSelectedWord, hpvalid, hphead,
          hpeval, hselectedLe⟩
      let replacements :=
        (annotateTwoFrom t 0 promotedSchedule).map (relabelPair j)
      have hreplacementsLength :
          replacements.length = selectedTrace.length := by
        calc
          replacements.length = promotedSchedule.length := by
            simp [replacements, annotateTwoFrom_length]
          _ = promotedSchedule.count Side.first +
                promotedSchedule.count Side.second :=
            by
              rw [List.length_eq_countP_add_countP
                (p := fun side : Side => side == Side.first),
                List.count_eq_countP, List.count_eq_countP]
              congr 1
              apply congrArg (fun predicate => promotedSchedule.countP predicate)
              funext side
              cases side <;> rfl
          _ = (u.drop t).length + (tail.getD j []).length := by
            rw [hpvalid.1, hpvalid.2]
          _ = schedule.count Side.first + schedule.count Side.second := by
            rw [hscheduleValid.1, hscheduleValid.2]
          _ = schedule.length := by
            rw [List.length_eq_countP_add_countP
              (p := fun side : Side => side == Side.first),
              List.count_eq_countP, List.count_eq_countP]
            congr 1
            apply congrArg (fun predicate => schedule.countP predicate)
            funext side
            cases side <;> rfl
          _ = selectedTrace.length := by simp [schedule]
      have hreplacementsSelected : ∀ replacement ∈ replacements,
          selectsPair j replacement = true := by
        intro replacement hreplacement
        simp only [replacements, List.mem_map] at hreplacement
        rcases hreplacement with ⟨entry, _, rfl⟩
        rcases entry with ⟨side, occurrence⟩
        cases side <;> simp [relabelPair, selectsPair]
      rcases refillWhere_spec (selectsPair j) replacements trace
          (by simpa [selectedTrace] using hreplacementsLength)
          hreplacementsSelected with
        ⟨promoted, hfill, hmask, hpselected, hpother⟩
      have hpfirst : replacements.filter (fun entry => entry.1 = 0) =
          occurrenceRun 0 t (u.length - t) := by
        rw [filter_relabel_annotate_first, hpvalid.1]
        simp [ht]
      have hpsecond :
          replacements.filter (fun entry => entry.1 = j + 1) =
            occurrenceRun (j + 1) 0 (tail.getD j []).length := by
        rw [filter_relabel_annotate_second, hpvalid.2]
      have hpTraceValid : TraceValidFrom (u :: tail)
          (fun i => if i = 0 then t else 0) promoted := by
        intro i
        by_cases hi0 : i = 0
        · subst i
          rw [← filterSelectedZero promoted, hpselected, hpfirst]
          simp [ht]
        · by_cases hij : i = j + 1
          · subst i
            rw [← filterSelectedSecond promoted, hpselected, hpsecond]
            simp
          · rw [← filterUnselectedOther i hi0 hij promoted, hpother,
              filterUnselectedOther i hi0 hij trace]
            exact hvalid i
      have hpheadTrace : promoted.head? = some (0, t) := by
        cases promotedSchedule with
        | nil => simp at hphead
        | cons side promotedSchedule =>
            have hside : side = Side.first := by simpa using hphead
            subst side
            simp [replacements, annotateTwoFrom, relabelPair, trace,
              refillWhere, selectsPair] at hfill
            rcases hfill with ⟨filled, _, hpromoted⟩
            rw [← hpromoted]
            rfl
      have hused : ∀ i,
          (if i = 0 then t else 0) ≤ ((u :: tail).getD i []).length := by
        intro i
        by_cases hi : i = 0
        · subst i
          simpa using ht
        · simp [hi]
      rcases trace_read_exists (u :: tail)
          (fun i => if i = 0 then t else 0) promoted hused hpTraceValid with
        ⟨promotedWord, hpread⟩
      have hpselectedRead : replacements.mapM (readIndexed (u :: tail)) =
          some promotedSelectedWord := by
        rw [readPair]
        exact hpeval
      rcases mapM_filter_exists trace (fun entry => !selectsPair j entry)
          (readIndexed (u :: tail)) word heval with
        ⟨otherWord, hotherRead⟩
      refine ⟨promoted, promotedWord, hpTraceValid, hpheadTrace, hpread, ?_⟩
      exact refillWhere_mapM_mono (selectsPair j)
        (readIndexed (u :: tail)) replacements trace promoted word promotedWord
        selectedWord promotedSelectedWord otherWord
        (by simpa [selectedTrace] using hreplacementsLength)
        hreplacementsSelected hfill heval hpread hselectedRead hpselectedRead
        hotherRead hselectedLe

private def lowerEntry : Nat × Nat → Nat × Nat
  | (i, occurrence) => (i - 1, occurrence)

private theorem lower_occurrenceRun (i start count : Nat) :
    (occurrenceRun (i + 1) start count).map lowerEntry =
      occurrenceRun i start count := by
  induction count generalizing i start with
  | zero => rfl
  | succ count ih => simp [occurrenceRun, lowerEntry, ih]

private theorem filter_lower_trace (trace : List (Nat × Nat))
    (hpositive : ∀ entry ∈ trace, 0 < entry.1) (i : Nat) :
    (trace.map lowerEntry).filter (fun entry => entry.1 = i) =
      (trace.filter (fun entry => entry.1 = i + 1)).map lowerEntry := by
  induction trace with
  | nil => rfl
  | cons entry trace ih =>
      rcases entry with ⟨label, occurrence⟩
      have hlabel := hpositive (label, occurrence) (by simp)
      have htail : ∀ entry ∈ trace, 0 < entry.1 := by
        intro item hitem
        exact hpositive item (by simp [hitem])
      by_cases hi : label = i + 1
      · subst label
        simp [lowerEntry, ih htail]
      · have hsub : label - 1 ≠ i := by omega
        simp [lowerEntry, hi, hsub, ih htail]

private theorem lower_trace_read (u : List A) (tail : List (List A))
    (trace : List (Nat × Nat))
    (hpositive : ∀ entry ∈ trace, 0 < entry.1) :
    (trace.map lowerEntry).mapM (readIndexed tail) =
      trace.mapM (readIndexed (u :: tail)) := by
  induction trace with
  | nil => rfl
  | cons entry trace ih =>
      rcases entry with ⟨label, occurrence⟩
      have hlabel := hpositive (label, occurrence) (by simp)
      have htail : ∀ entry ∈ trace, 0 < entry.1 := by
        intro item hitem
        exact hpositive item (by simp [hitem])
      cases label with
      | zero => omega
      | succ label => simp [lowerEntry, readIndexed, ih htail]

private theorem trace_le_flatten_aux [LinearOrder A]
    (u : List A) (tail : List (List A))
    (hu : IsLyndon u) (htail : ∀ v ∈ tail, IsLyndon v)
    (huge : ∀ v ∈ tail, u ≥ v) (hpair : tail.Pairwise (· ≥ ·))
    (t : Nat) (ht : t ≤ u.length) (trace : List (Nat × Nat))
    (word : List A)
    (hvalid : TraceValidFrom (u :: tail)
      (fun i => if i = 0 then t else 0) trace)
    (heval : trace.mapM (readIndexed (u :: tail)) = some word) :
    word ≤ u.drop t ++ tail.flatten := by
  classical
  by_cases hdone : t = u.length
  · have hnozero : ∀ entry ∈ trace, 0 < entry.1 := by
      rintro ⟨label, occurrence⟩ hmem
      cases label with
      | zero =>
          have hm : (0, occurrence) ∈
              trace.filter (fun entry => entry.1 = 0) := by simp [hmem]
          rw [hvalid 0] at hm
          simp [hdone, occurrenceRun] at hm
      | succ label => omega
    cases tail with
    | nil =>
        have htrace : trace = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          rintro ⟨label, occurrence⟩ hmem
          have hm : (label, occurrence) ∈
              trace.filter (fun entry => entry.1 = label) := by simp [hmem]
          rw [hvalid label] at hm
          cases label <;> simp [hdone, occurrenceRun] at hm
        subst trace
        simp at heval
        subst word
        simp [hdone]
    | cons v rest =>
        have hlowerValid : TraceValidFrom (v :: rest) (fun _ => 0)
            (trace.map lowerEntry) := by
          intro i
          rw [filter_lower_trace trace hnozero i, hvalid (i + 1)]
          simp [lower_occurrenceRun]
        have hlowerEval : (trace.map lowerEntry).mapM
            (readIndexed (v :: rest)) = some word := by
          rw [lower_trace_read u (v :: rest) trace hnozero]
          exact heval
        have hp := List.pairwise_cons.mp hpair
        have hrec := trace_le_flatten_aux v rest (htail v (by simp))
          (fun z hz => htail z (by simp [hz])) hp.1 hp.2 0 (by simp)
          (trace.map lowerEntry) word (by simpa using hlowerValid) hlowerEval
        simpa [hdone] using hrec
  · have hlt : t < u.length := lt_of_le_of_ne ht hdone
    have consume : ∀ rest restWord,
        TraceValidFrom (u :: tail) (fun i => if i = 0 then t else 0)
          ((0, t) :: rest) →
        ((0, t) :: rest).mapM (readIndexed (u :: tail)) = some restWord →
        restWord ≤ u.drop t ++ tail.flatten := by
      intro rest restWord hv he
      have hvrest : TraceValidFrom (u :: tail)
          (fun i => if i = 0 then t + 1 else 0) rest := by
        intro i
        by_cases hi : i = 0
        · subst i
          have h := hv 0
          have hc := congrArg List.tail h
          simp only [if_pos, List.getD_cons_zero]
          cases hs : u.length - t with
          | zero => omega
          | succ count =>
              have hn : u.length - (t + 1) = count := by omega
              rw [hn]
              simpa [hs, occurrenceRun] using hc
        · have h0i : 0 ≠ i := Ne.symm hi
          simpa [hi, h0i] using hv i
      cases hr : rest.mapM (readIndexed (u :: tail)) with
      | none => simp [readIndexed, List.getElem?_eq_getElem hlt, hr] at he
      | some suffix =>
          have hw : restWord = u[t] :: suffix := by
            simpa [readIndexed, List.getElem?_eq_getElem hlt, hr] using he.symm
          subst restWord
          have hrec := trace_le_flatten_aux u tail hu htail huge hpair
            (t + 1) (by omega) rest suffix hvrest hr
          rw [List.drop_eq_getElem_cons hlt]
          exact List.cons_le_cons u[t] hrec
    cases trace with
    | nil =>
        have h := hvalid 0
        have hpos : 0 < u.length - t := by omega
        cases hc : u.length - t with
        | zero => omega
        | succ count => simp [hc, occurrenceRun] at h
    | cons entry rest =>
        rcases entry with ⟨label, occurrence⟩
        cases label with
        | zero =>
            have ho : occurrence = t := by
              have h := congrArg List.head? (hvalid 0)
              cases hc : u.length - t with
              | zero => omega
              | succ count => simpa [hc, occurrenceRun] using h
            subst occurrence
            exact consume rest word hvalid heval
        | succ j =>
            have ho : occurrence = 0 := by
              have h := congrArg List.head? (hvalid (j + 1))
              simp only [List.filter_cons, decide_true, List.getD_cons_succ] at h
              cases hc : (tail.getD j []).length with
              | zero => rw [hc] at h; simp [occurrenceRun] at h
              | succ count =>
                  rw [hc] at h
                  simpa [occurrenceRun] using h
            subst occurrence
            have hugetD : u ≥ tail.getD j [] := by
              have getD_order : ∀ (xs : List (List A)),
                  (∀ z ∈ xs, u ≥ z) → ∀ n, u ≥ xs.getD n [] := by
                intro xs hall n
                induction xs generalizing n with
                | nil =>
                    cases u with
                    | nil => exact le_rfl
                    | cons a u => exact le_of_lt List.Lex.nil
                | cons v rest ih =>
                    cases n with
                    | zero => simpa using hall v (by simp)
                    | succ n =>
                        simp only [List.getD_cons_succ]
                        exact ih (fun z hz => hall z (by simp [hz])) n
              exact getD_order tail huge j
            have hdropNe : u.drop t ≠ [] := by
              intro heq
              have hh := congrArg List.length heq
              simp at hh
              omega
            have hdrop : u.drop t ≥ u := by
              have hsuffix : u.drop t <:+ u :=
                ⟨u.take t, List.take_append_drop t u⟩
              rcases eq_or_ne (u.drop t) u with heq | hne
              · exact heq.ge
              · exact ((isLyndon_iff_lt_suffix u).mp hu).2
                  (u.drop t) hdropNe hsuffix hne |>.le
            rcases promote_trace_front u tail t j ((j + 1, 0) :: rest)
                word ht hvalid rfl (hugetD.trans hdrop) heval with
              ⟨promoted, promotedWord, hpvalid, hphead, hpeval, hle⟩
            cases promoted with
            | nil => simp at hphead
            | cons entry promoted =>
                have he : entry = (0, t) := by simpa using hphead
                subst entry
                exact hle.trans (consume promoted promotedWord hpvalid hpeval)
termination_by
  (u.length - t + (tail.map List.length).sum) * 2 + tail.length + 1
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [List.map_cons, List.sum_cons, List.length_cons]
  all_goals omega

/-- Every indexed interleaving of nonincreasing Lyndon factors is bounded by concatenation. -/
theorem evaluateSchedule_le_flatten [LinearOrder A]
    (factors : List (List A)) (schedule : IndexedSchedule) (word : List A)
    (hlyndon : ∀ u ∈ factors, IsLyndon u) (hpair : factors.Pairwise (· ≥ ·))
    (hvalid : IsValidSchedule factors schedule) (heval : evaluateSchedule factors schedule = some word) :
    word ≤ factors.flatten := by
  classical
  unfold evaluateSchedule at heval
  simp only [dif_pos hvalid] at heval
  cases factors with
  | nil =>
      have hs : schedule = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro i hi
        have hp := List.count_pos_iff.mpr hi
        rw [hvalid i] at hp
        simp at hp
      subst schedule
      have hw : word = [] := by
        simpa [annotateIndexed, annotateIndexedFrom] using heval.symm
      subst word
      exact le_rfl
  | cons u tail =>
      have hp := List.pairwise_cons.mp hpair
      exact trace_le_flatten_aux u tail (hlyndon u (by simp))
        (fun v hv => hlyndon v (by simp [hv])) hp.1 hp.2 0 (by simp)
        (annotateIndexed schedule) word
        (by
          intro i
          rw [annotateIndexed, filter_annotateIndexedFrom, hvalid]
          simp)
        heval

end D5.S1.Words.Complexity.LyndonIndexedShuffleOrder

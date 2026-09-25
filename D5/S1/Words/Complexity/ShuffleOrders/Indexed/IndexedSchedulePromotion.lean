/- GID: D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedSchedulePromotion
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedSchedulePromotion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary front promotion lifts to one selected pair of indexed sources. -/

import D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleWeave

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedSchedulePromotion

open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder
open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleEvaluation
open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryFrontPromotion
open D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleOrder
open private TraceValidFrom filter_relabel_annotate_first
  filter_relabel_annotate_second mapM_filter_exists occurrenceRun pairSide
  pair_trace_eq_annotateTwoFrom relabelPair selectsPair occurrenceRun_length
  trace_read_exists from
  D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleOrder
open private refillWhere refillWhere_mapM_mono refillWhere_spec from
  D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleWeave

variable {A : Type*}

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


end D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedSchedulePromotion

/- GID: D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedShuffleOrder
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedShuffleOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Indexed Lyndon schedule evaluation is bounded by factor concatenation. -/

import D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
import D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedSchedulePromotion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedShuffleOrder

open D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
open D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleOrder
open private TraceValidFrom filter_annotateIndexedFrom occurrenceRun from
  D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleOrder
open private promote_trace_front from
  D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedSchedulePromotion

variable {A : Type*}

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


end D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedShuffleOrder

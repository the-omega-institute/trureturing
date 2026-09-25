/- GID: D5/S1/Words/Complexity/ExactDecks/UpperBound/ShuffleScheduleComposition
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/ExactDecks/UpperBound/ShuffleScheduleComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Binary schedules compose into valid indexed schedules for all factors. -/

import D5.S1.Words.Complexity.ExactDecks.UpperBound.LyndonFactorization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ExactDecks.UpperBound.ShuffleScheduleComposition

open D5.S1.Words.Complexity.VivionBinomialConverseFails
open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder
open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleEvaluation
open D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleOrder
open D5.S1.Words.Complexity.ShuffleOrders.Indexed.IndexedScheduleWeave
open D5.S1.Words.Complexity.ExactDecks.UpperBound.OverlapInfiltration

variable {A : Type*}

private def iteratedOverlapInfiltrations [DecidableEq A] :
    List (List A) → List (List A)
  | [] => [[]]
  | word :: factors =>
      (iteratedOverlapInfiltrations factors).flatMap (overlapInfiltrations word)
private def iteratedOrdinaryShuffles : List (List A) → List (List A)
  | [] => [[]]
  | word :: factors =>
      (iteratedOrdinaryShuffles factors).flatMap (ordinaryShuffles word)
private def composeIndexed : List Side → List Nat → List Nat
  | [], _ => []
  | Side.first :: binary, tail => 0 :: composeIndexed binary tail
  | Side.second :: binary, [] => []
  | Side.second :: binary, i :: tail => (i + 1) :: composeIndexed binary tail
private theorem composeIndexed_counts (binary : List Side) (tail : List Nat)
    (hlength : binary.count Side.second = tail.length) :
    (composeIndexed binary tail).count 0 = binary.count Side.first ∧
      ∀ i, (composeIndexed binary tail).count (i + 1) = tail.count i := by
  induction binary generalizing tail with
  | nil =>
      have : tail = [] := by simpa using hlength.symm
      subst tail; simp [composeIndexed]
  | cons side binary ih =>
      cases side with
      | first =>
          have htail : binary.count Side.second = tail.length := by simpa using hlength
          rcases ih tail htail with ⟨hzero, hsucc⟩
          refine ⟨by simp [composeIndexed, hzero], ?_⟩
          intro i; simp [composeIndexed, hsucc i]
      | second =>
          cases tail with
          | nil => simp at hlength
          | cons label tail =>
              have htail : binary.count Side.second = tail.length := by simpa using hlength
              rcases ih tail htail with ⟨hzero, hsucc⟩
              refine ⟨by simp [composeIndexed, hzero], ?_⟩
              intro i; by_cases hi : label = i
              · subst label
                simp [composeIndexed, hsucc]
              · have hil : label + 1 ≠ i + 1 := by omega
                simp [composeIndexed, hil, hi, hsucc]
private theorem mem_ordinaryShuffles_schedule :
    ∀ (left right merged : List A), merged ∈ ordinaryShuffles left right →
      ∃ schedule, ValidTwoSchedule left right schedule ∧
        evaluateTwo left right schedule = some merged := by
  intro left
  induction left with
  | nil =>
      intro right
      induction right with
      | nil =>
          intro merged hmerged
          have : merged = [] := by simpa [ordinaryShuffles] using hmerged
          subst merged
          exact ⟨[], by simp [ValidTwoSchedule], rfl⟩
      | cons b right ih =>
          intro merged hmerged
          have hmerged' : merged = b :: right := by simpa [ordinaryShuffles] using hmerged
          subst merged
          rcases ih right (by simp [ordinaryShuffles]) with ⟨schedule, hvalid, heval⟩
          refine ⟨Side.second :: schedule,
            by simpa [ValidTwoSchedule] using hvalid, ?_⟩
          unfold evaluateTwo annotateTwo at heval ⊢
          simp only [annotateTwoFrom, readTwo, List.getElem?_cons_zero,
            List.mapM_cons]
          rw [annotateTwoFrom_add 0 1 schedule 0 0, List.mapM_map]
          have hread : readTwo ([] : List A) (b :: right) ∘
              shiftPairOccurrences 0 1 = readTwo [] right := by
            funext ⟨side, occurrence⟩
            cases side <;> simp [Function.comp_apply, shiftPairOccurrences,
              readTwo, Nat.add_comm, List.getElem?_cons_succ]
          rw [hread, heval]
          rfl
  | cons a left ihLeft =>
      intro right
      induction right with
      | nil =>
          intro merged hmerged
          have hmerged' : merged = a :: left := by simpa [ordinaryShuffles] using hmerged
          subst merged
          have hleftMem : left ∈ ordinaryShuffles left [] := by
            cases left <;> simp [ordinaryShuffles]
          rcases ihLeft [] left hleftMem with ⟨schedule, hvalid, heval⟩
          refine ⟨Side.first :: schedule,
            by simpa [ValidTwoSchedule] using hvalid, ?_⟩
          unfold evaluateTwo annotateTwo at heval ⊢
          simp only [annotateTwoFrom, readTwo, List.getElem?_cons_zero,
            List.mapM_cons]
          have hshift : annotateTwoFrom 1 0 schedule = (annotateTwo schedule).map (shiftPairOccurrences 1 0) := by
            simpa [annotateTwo] using annotateTwoFrom_add 1 0 schedule 0 0
          rw [hshift, List.mapM_map]
          have hread : readTwo (a :: left) ([] : List A) ∘
              shiftPairOccurrences 1 0 = readTwo left [] := by
            funext ⟨side, occurrence⟩
            cases side <;> simp [Function.comp_apply, shiftPairOccurrences,
              readTwo, Nat.add_comm, List.getElem?_cons_succ]
          rw [hread]
          simp only [annotateTwo]
          rw [heval]
          rfl
      | cons b right ihRight =>
          intro merged hmerged
          rw [ordinaryShuffles, List.mem_append] at hmerged
          rcases hmerged with hfirst | hsecond
          · rw [List.mem_map] at hfirst
            rcases hfirst with ⟨middle, hmiddle, rfl⟩
            rcases ihLeft (b :: right) middle hmiddle with ⟨schedule, hvalid, heval⟩
            refine ⟨Side.first :: schedule,
              by simpa [ValidTwoSchedule] using hvalid, ?_⟩
            unfold evaluateTwo annotateTwo at heval ⊢
            simp only [annotateTwoFrom, readTwo, List.getElem?_cons_zero,
              List.mapM_cons]
            have hshift : annotateTwoFrom 1 0 schedule = (annotateTwo schedule).map (shiftPairOccurrences 1 0) := by
              simpa [annotateTwo] using annotateTwoFrom_add 1 0 schedule 0 0
            rw [hshift, List.mapM_map]
            have hread : readTwo (a :: left) (b :: right) ∘
                shiftPairOccurrences 1 0 = readTwo left (b :: right) := by
              funext ⟨side, occurrence⟩
              cases side <;> simp [Function.comp_apply, shiftPairOccurrences,
                readTwo, Nat.add_comm, List.getElem?_cons_succ]
            rw [hread]
            simp only [annotateTwo]
            rw [heval]
            rfl
          · rw [List.mem_map] at hsecond
            rcases hsecond with ⟨middle, hmiddle, rfl⟩
            rcases ihRight middle hmiddle with ⟨schedule, hvalid, heval⟩
            refine ⟨Side.second :: schedule,
              by simpa [ValidTwoSchedule] using hvalid, ?_⟩
            unfold evaluateTwo annotateTwo at heval ⊢
            simp only [annotateTwoFrom, readTwo, List.getElem?_cons_zero,
              List.mapM_cons]
            rw [annotateTwoFrom_add 0 1 schedule 0 0, List.mapM_map]
            have hread : readTwo (a :: left) (b :: right) ∘
                shiftPairOccurrences 0 1 = readTwo (a :: left) right := by
              funext ⟨side, occurrence⟩
              cases side <;> simp [Function.comp_apply, shiftPairOccurrences,
                readTwo, Nat.add_comm, List.getElem?_cons_succ]
            rw [hread, heval]; rfl
private def combinedUsed (firstUsed : Nat) (tailUsed : Nat → Nat) : Nat → Nat
  | 0 => firstUsed
  | i + 1 => tailUsed i
private def liftTailEntry : Nat × Nat → Nat × Nat
  | (i, occurrence) => (i + 1, occurrence)
private def composeTrace : List (Side × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], _ => []
  | (Side.first, occurrence) :: binary, tail =>
      (0, occurrence) :: composeTrace binary tail
  | (Side.second, _) :: binary, [] => []
  | (Side.second, _) :: binary, entry :: tail =>
      liftTailEntry entry :: composeTrace binary tail
private theorem annotate_composeIndexed (binary : List Side) (tail : List Nat)
    (firstUsed secondUsed : Nat) (tailUsed : Nat → Nat) :
    annotateIndexedFrom (combinedUsed firstUsed tailUsed) (composeIndexed binary tail) =
      composeTrace (annotateTwoFrom firstUsed secondUsed binary)
        (annotateIndexedFrom tailUsed tail) := by
  induction binary generalizing tail firstUsed secondUsed tailUsed with
  | nil => rfl
  | cons side binary ih =>
      cases side with
      | first =>
          have hupdate : Function.update (combinedUsed firstUsed tailUsed) 0
              (firstUsed + 1) = combinedUsed (firstUsed + 1) tailUsed := by
            funext i; cases i <;> simp [combinedUsed, Function.update]
          simp only [composeIndexed, annotateIndexedFrom, combinedUsed,
            annotateTwoFrom, composeTrace]
          rw [hupdate, ih]
      | second =>
          cases tail with
          | nil => rfl
          | cons label tail =>
              have hupdate : Function.update (combinedUsed firstUsed tailUsed)
                  (label + 1) (tailUsed label + 1) =
                combinedUsed firstUsed
                  (Function.update tailUsed label (tailUsed label + 1)) := by
                funext i
                cases i with
                | zero => simp [combinedUsed, Function.update]
                | succ i => simp [combinedUsed, Function.update, Nat.succ.injEq]
              simp only [composeIndexed, annotateIndexedFrom, combinedUsed,
                annotateTwoFrom, composeTrace, liftTailEntry]
              rw [hupdate, ih]
private theorem composeTrace_mapM (first : List A) (factors : List (List A))
    (middle : List A) (binary : List Side) (tailTrace : List (Nat × Nat))
    (firstUsed secondUsed : Nat) (hlength : binary.count Side.second = tailTrace.length)
    (htail : tailTrace.mapM (readIndexed factors) =
      some (middle.drop secondUsed)) :
    (composeTrace (annotateTwoFrom firstUsed secondUsed binary) tailTrace).mapM
        (readIndexed (first :: factors)) =
      (annotateTwoFrom firstUsed secondUsed binary).mapM
        (readTwo first middle) := by
  induction binary generalizing tailTrace firstUsed secondUsed with
  | nil =>
      have : tailTrace = [] := by
        simpa using List.length_eq_zero_iff.mp hlength.symm
      subst tailTrace; rfl
  | cons side binary ih =>
      cases side with
      | first =>
          have hlength' : binary.count Side.second = tailTrace.length := by simpa using hlength
          simp only [annotateTwoFrom, composeTrace, List.mapM_cons, readIndexed,
            List.getD_cons_zero, readTwo]
          rw [ih tailTrace (firstUsed + 1) secondUsed hlength' htail]
      | second =>
          cases tailTrace with
          | nil => simp at hlength
          | cons entry tailTrace =>
              have hlength' : binary.count Side.second = tailTrace.length := by simpa using hlength
              cases hread : readIndexed factors entry with
              | none => simp [hread] at htail
              | some value =>
                  cases hrest : tailTrace.mapM (readIndexed factors) with
                  | none => simp [hread, hrest] at htail
                  | some rest =>
                      have hdrop : middle.drop secondUsed = value :: rest := by
                        simpa [hread, hrest] using htail.symm
                      have hlt : secondUsed < middle.length := by
                        by_contra hnot
                        have hempty : middle.drop secondUsed = [] :=
                          List.drop_eq_nil_iff.mpr (Nat.le_of_not_gt hnot)
                        simp [hempty] at hdrop
                      have hparts : middle[secondUsed] = value ∧
                          middle.drop (secondUsed + 1) = rest := by
                        have := hdrop
                        rw [List.drop_eq_getElem_cons hlt] at this
                        exact List.cons.inj this
                      have hrec := ih tailTrace firstUsed (secondUsed + 1)
                        hlength' (hparts.2.symm ▸ hrest)
                      have hlift :
                          readIndexed (first :: factors) (liftTailEntry entry) =
                            readIndexed factors entry := by
                        rcases entry with ⟨i, occurrence⟩
                        simp [liftTailEntry, readIndexed]
                      simp only [annotateTwoFrom, composeTrace, List.mapM_cons]
                      rw [hlift, hread]
                      simp only [readTwo]
                      rw [List.getElem?_eq_getElem hlt, hparts.1, hrec]
private theorem composeIndexed_spec (first : List A) (factors : List (List A))
    (middle merged : List A)
    (binary : List Side) (tail : List Nat)
    (hbinaryValid : ValidTwoSchedule first middle binary)
    (hbinaryEval : evaluateTwo first middle binary = some merged)
    (htailValid : IsValidSchedule factors tail)
    (htailEval : evaluateSchedule factors tail = some middle) :
    IsValidSchedule (first :: factors) (composeIndexed binary tail) ∧
      evaluateSchedule (first :: factors) (composeIndexed binary tail) = some merged := by
  classical
  have htailRaw : (annotateIndexed tail).mapM (readIndexed factors) = some middle := by
    unfold evaluateSchedule at htailEval
    simpa [htailValid] using htailEval
  have hannLength : ∀ used schedule,
      (annotateIndexedFrom used schedule).length = schedule.length := by
    intro used schedule
    induction schedule generalizing used with
    | nil => rfl
    | cons i schedule ih => simp [annotateIndexedFrom, ih]
  have htailLength : tail.length = middle.length := by
    have h := mapM_length (readIndexed factors) (annotateIndexed tail)
      middle htailRaw
    simpa [annotateIndexed, hannLength] using h.symm
  have hcounts := composeIndexed_counts binary tail
    (by rw [hbinaryValid.2, htailLength])
  have hvalid : IsValidSchedule (first :: factors)
      (composeIndexed binary tail) := by
    intro i
    cases i with
    | zero => simpa using hcounts.1.trans hbinaryValid.1
    | succ i => simpa using (hcounts.2 i).trans (htailValid i)
  refine ⟨hvalid, ?_⟩
  unfold evaluateSchedule
  simp only [dif_pos hvalid]
  have hzero : combinedUsed 0 (fun _ => 0) = (fun _ => 0) := by
    funext i; cases i <;> rfl
  rw [annotateIndexed, ← hzero,
    annotate_composeIndexed binary tail 0 0 (fun _ => 0)]
  have htraceLength : binary.count Side.second =
      (annotateIndexed tail).length := by
    rw [hbinaryValid.2, ← htailLength]
    exact (hannLength (fun _ => 0) tail).symm
  have htrace := composeTrace_mapM first factors middle binary
    (annotateIndexed tail) 0 0 htraceLength (by simpa using htailRaw)
  change (composeTrace (annotateTwoFrom 0 0 binary)
      (annotateIndexed tail)).mapM (readIndexed (first :: factors)) =
    some merged
  rw [htrace]
  simpa [evaluateTwo, annotateTwo] using hbinaryEval
private theorem mem_iteratedOrdinaryShuffles_schedule :
    ∀ (factors : List (List A)) (merged : List A), merged ∈ iteratedOrdinaryShuffles factors →
      ∃ schedule, IsValidSchedule factors schedule ∧
        evaluateSchedule factors schedule = some merged := by
  intro factors
  induction factors with
  | nil =>
      intro merged hmerged
      have : merged = [] := by simpa [iteratedOrdinaryShuffles] using hmerged
      subst merged
      have hvalid : IsValidSchedule ([] : List (List A)) [] := by simp [IsValidSchedule]
      exact ⟨[], hvalid, by simp [evaluateSchedule, hvalid, annotateIndexed,
        annotateIndexedFrom]⟩
  | cons first factors ih =>
      intro merged hmerged
      simp only [iteratedOrdinaryShuffles, List.mem_flatMap] at hmerged
      obtain ⟨middle, hmiddle, hmerged⟩ := hmerged
      obtain ⟨tail, htailValid, htailEval⟩ := ih middle hmiddle
      obtain ⟨binary, hbinaryValid, hbinaryEval⟩ :=
        mem_ordinaryShuffles_schedule first middle merged hmerged
      obtain ⟨hvalid, heval⟩ := composeIndexed_spec first factors middle merged
        binary tail hbinaryValid hbinaryEval htailValid htailEval
      exact ⟨composeIndexed binary tail, hvalid, heval⟩

end D5.S1.Words.Complexity.ExactDecks.UpperBound.ShuffleScheduleComposition

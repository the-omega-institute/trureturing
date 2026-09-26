/- GID: D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryFrontPromotion
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/ShuffleOrders/Binary/BinaryFrontPromotion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A smaller leading source can be promoted without decreasing evaluation. -/

import D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleEvaluation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryFrontPromotion

open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder
open D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleEvaluation
open private first_return_or_always_ahead second_count_gt_first_count swapSide from
  D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleOrder
open private evaluateTwo_exists exists_difference_before_of_length_lt_of_ge
  second_occurrence_split swapped_balanced_prefix_equal swapped_prefix_strict from
  D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryScheduleEvaluation

variable {A : Type*}

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


end D5.S1.Words.Complexity.ShuffleOrders.Binary.BinaryFrontPromotion

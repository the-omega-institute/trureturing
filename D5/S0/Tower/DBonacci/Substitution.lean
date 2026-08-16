/- GID: D5/S0/Tower/DBonacci/Substitution
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/Substitution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: D-bonacci gap refinement sends zero to top and successor to top-predecessor. -/

import D5.S0.Tower.DBonacci.Gaps
import D5.S0.Tower.Tribonacci.Substitution

namespace D5.S0.Tower.DBonacci.Substitution

open D5.S0.Tower.DBonacci.Names
open D5.S0.Tower.DBonacci.PerronRoot
open D5.S0.Tower.DBonacci.Values
open D5.S0.Tower.DBonacci.Gaps

/-- Removing the first digit commutes with adjoining a final false digit. -/
theorem tail_snoc_false (n : Nat) (word : Fin (n + 1) -> Bool) :
    Fin.tail (Fin.snoc word false : Fin (n + 2) -> Bool) =
      (Fin.snoc (Fin.tail word) false : Fin (n + 1) -> Bool) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Fin.tail]
  · simp only [Fin.tail, Fin.snoc_castSucc]
    exact (congrArg (Fin.snoc word false : Fin (n + 2) -> Bool)
      (show j.castSucc.succ = (j.succ).castSucc by apply Fin.ext; rfl)).trans
        (by simp only [Fin.snoc_castSucc])

/-- Adjoining a final false digit preserves every run-budget state. -/
theorem runAdmissible_snoc_false (maxTrue fuel Q : Nat) (word : Fin Q -> Bool)
    (hadmissible : runAdmissible maxTrue fuel Q word = true) :
    runAdmissible maxTrue fuel (Q + 1) (Fin.snoc word false) = true := by
  induction Q generalizing fuel with
  | zero =>
      have hword : Fin.snoc word false = (fun _ : Fin 1 => false) := by
        funext i
        rw [show i = Fin.last 0 by apply Fin.ext; omega, Fin.snoc_last]
      rw [hword]
      cases fuel <;> simp [runAdmissible]
  | succ Q ih =>
      have hzero :
          (Fin.snoc word false : Fin (Q + 2) -> Bool) 0 = word 0 := by
        rw [show (0 : Fin (Q + 2)) = (0 : Fin (Q + 1)).castSucc by
          apply Fin.ext; rfl, Fin.snoc_castSucc]
      cases fuel with
      | zero =>
          by_cases hhead : word 0
          · simp [runAdmissible, hhead] at hadmissible
          · simp only [runAdmissible, hzero, hhead, Bool.false_eq_true,
              ↓reduceIte] at hadmissible ⊢
            rw [tail_snoc_false]
            exact ih maxTrue (Fin.tail word) hadmissible
      | succ fuel =>
          by_cases hhead : word 0
          · simp only [runAdmissible, hzero, hhead, ↓reduceIte]
                at hadmissible ⊢
            rw [tail_snoc_false]
            exact ih fuel (Fin.tail word) hadmissible
          · simp only [runAdmissible, hzero, hhead, Bool.false_eq_true,
              ↓reduceIte] at hadmissible ⊢
            rw [tail_snoc_false]
            exact ih maxTrue (Fin.tail word) hadmissible

/-- Removing the final digit preserves every run-budget state. -/
theorem runAdmissible_init (maxTrue fuel Q : Nat) (word : Fin (Q + 1) -> Bool)
    (hadmissible : runAdmissible maxTrue fuel (Q + 1) word = true) :
    runAdmissible maxTrue fuel Q (Fin.init word) = true := by
  induction Q generalizing fuel with
  | zero => simp [runAdmissible]
  | succ Q ih =>
      have hzero : word (Fin.castSucc (0 : Fin (Q + 1))) = word 0 := by
        congr 1
      cases fuel with
      | zero =>
          by_cases hhead : word 0
          · simp [runAdmissible, hhead] at hadmissible
          · simp only [runAdmissible, Fin.init, hzero, hhead, Bool.false_eq_true,
                ↓reduceIte]
                at hadmissible ⊢
            rw [Fin.tail_init_eq_init_tail]
            exact ih maxTrue (Fin.tail word) hadmissible
      | succ fuel =>
          by_cases hhead : word 0
          · simp only [runAdmissible, Fin.init, hzero, hhead, ↓reduceIte]
                at hadmissible ⊢
            rw [Fin.tail_init_eq_init_tail]
            exact ih fuel (Fin.tail word) hadmissible
          · simp only [runAdmissible, Fin.init, hzero, hhead, Bool.false_eq_true,
                ↓reduceIte]
                at hadmissible ⊢
            rw [Fin.tail_init_eq_init_tail]
            exact ih maxTrue (Fin.tail word) hadmissible

theorem admissible_snoc_false (d Q : Nat) (word : Fin Q -> Bool)
    (hadmissible : DBonacciAdmissible d Q word) :
    DBonacciAdmissible d (Q + 1) (Fin.snoc word false) := by
  cases d with
  | zero => exact False.elim hadmissible
  | succ maxTrue => exact runAdmissible_snoc_false maxTrue maxTrue Q word hadmissible

theorem admissible_init (d Q : Nat) (word : Fin (Q + 1) -> Bool)
    (hadmissible : DBonacciAdmissible d (Q + 1) word) :
    DBonacciAdmissible d Q (Fin.init word) := by
  cases d with
  | zero => exact False.elim hadmissible
  | succ maxTrue => exact runAdmissible_init maxTrue maxTrue Q word hadmissible

theorem dbonacciWordValue_snoc (d Q : Nat) (word : Fin Q -> Bool) (last : Bool) :
    dbonacciWordValue d (Q + 1) (Fin.snoc word last) =
      dbonacciWordValue d Q word +
        (if last then (dbonacciPerronRoot d)⁻¹ ^ (Q + 1) else 0) := by
  unfold dbonacciWordValue
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]

/-- A level-`Q` name embedded at level `Q+1` by adjoining a final zero. -/
def extendedName (d Q : Nat) (name : DBonacciName d Q) : DBonacciName d (Q + 1) :=
  ⟨Fin.snoc name.1 false, admissible_snoc_false d Q name.1 name.2⟩

/-- A fine name with its final digit removed. -/
def truncatedName (d Q : Nat) (name : DBonacciName d (Q + 1)) : DBonacciName d Q :=
  ⟨Fin.init name.1, admissible_init d Q name.1 name.2⟩

theorem extendedName_value (d Q : Nat) (name : DBonacciName d Q) :
    dbonacciNameValue d (Q + 1) (extendedName d Q name) =
      dbonacciNameValue d Q name := by
  change dbonacciWordValue d (Q + 1) (Fin.snoc name.1 false) =
    dbonacciWordValue d Q name.1
  rw [dbonacciWordValue_snoc]
  simp

theorem truncatedName_value (d Q : Nat) (name : DBonacciName d (Q + 1)) :
    dbonacciNameValue d (Q + 1) name =
      dbonacciNameValue d Q (truncatedName d Q name) +
        (if name.1 (Fin.last Q) then (dbonacciPerronRoot d)⁻¹ ^ (Q + 1) else 0) := by
  change dbonacciWordValue d (Q + 1) name.1 =
    dbonacciWordValue d Q (Fin.init name.1) + _
  conv_lhs => rw [← Fin.snoc_init_self name.1]
  exact dbonacciWordValue_snoc d Q (Fin.init name.1) (name.1 (Fin.last Q))

/-- The index at level `Q+1` of the old name with the same value. -/
noncomputable def levelEmbedding (d Q : Nat) (i : Fin (dbonacci d (Q + 2))) :
    Fin (dbonacci d (Q + 3)) :=
  (dbonacciIndexEquiv d (Q + 1)).symm
    (extendedName d Q (dbonacciIndexEquiv d Q i))

theorem levelEmbedding_value (d Q : Nat) (i : Fin (dbonacci d (Q + 2))) :
    indexedNameValue d (Q + 1) (levelEmbedding d Q i) =
      indexedNameValue d Q i := by
  change dbonacciNameValue d (Q + 1)
      (dbonacciIndexEquiv d (Q + 1)
        ((dbonacciIndexEquiv d (Q + 1)).symm
          (extendedName d Q (dbonacciIndexEquiv d Q i)))) =
    dbonacciNameValue d Q (dbonacciIndexEquiv d Q i)
  rw [(dbonacciIndexEquiv d (Q + 1)).apply_symm_apply]
  exact extendedName_value d Q (dbonacciIndexEquiv d Q i)

theorem levelEmbedding_strictMono (d Q : Nat) (hd : 2 ≤ d) :
    StrictMono (levelEmbedding d Q) := by
  intro i j hij
  apply ((indexed_nameValue_strictMono d (Q + 1) hd).lt_iff_lt).mp
  rw [levelEmbedding_value, levelEmbedding_value]
  exact indexed_nameValue_strictMono d Q hd hij

theorem extended_truncated_eq_of_last_false (d Q : Nat)
    (name : DBonacciName d (Q + 1)) (hlast : name.1 (Fin.last Q) = false) :
    extendedName d Q (truncatedName d Q name) = name := by
  apply Subtype.ext
  change Fin.snoc (Fin.init name.1) false = name.1
  rw [← hlast, Fin.snoc_init_self]

/-- The old indices are exactly the fine names whose newly appended digit is false. -/
theorem exists_levelEmbedding_iff_last_false (d Q : Nat)
    (j : Fin (dbonacci d (Q + 3))) :
    (∃ i, levelEmbedding d Q i = j) ↔
      (dbonacciIndexEquiv d (Q + 1) j).1 (Fin.last Q) = false := by
  constructor
  · rintro ⟨i, rfl⟩
    change (dbonacciIndexEquiv d (Q + 1)
      ((dbonacciIndexEquiv d (Q + 1)).symm
        (extendedName d Q (dbonacciIndexEquiv d Q i)))).1 (Fin.last Q) = false
    rw [(dbonacciIndexEquiv d (Q + 1)).apply_symm_apply]
    simp [extendedName]
  · intro hlast
    let fineName := dbonacciIndexEquiv d (Q + 1) j
    refine ⟨(dbonacciIndexEquiv d Q).symm (truncatedName d Q fineName), ?_⟩
    unfold levelEmbedding
    rw [(dbonacciIndexEquiv d Q).apply_symm_apply]
    apply (dbonacciIndexEquiv d (Q + 1)).injective
    rw [(dbonacciIndexEquiv d (Q + 1)).apply_symm_apply]
    exact extended_truncated_eq_of_last_false d Q fineName hlast

/-- Relative to level `Q`, the new level-`Q+1` names are exactly those ending in true. -/
theorem new_index_iff_last_true (d Q : Nat) (j : Fin (dbonacci d (Q + 3))) :
    (¬ ∃ i, levelEmbedding d Q i = j) ↔
      (dbonacciIndexEquiv d (Q + 1) j).1 (Fin.last Q) = true := by
  rw [exists_levelEmbedding_iff_last_false]
  cases (dbonacciIndexEquiv d (Q + 1) j).1 (Fin.last Q) <;> simp

/-- The left endpoint of a coarse adjacent gap. -/
def gapLeft (d Q : Nat) (i : Fin (dbonacci d (Q + 2) - 1)) :
    Fin (dbonacci d (Q + 2)) :=
  ⟨i.1, lt_of_lt_of_le i.2 (Nat.sub_le _ _)⟩

/-- The right endpoint of a coarse adjacent gap. -/
def gapRight (d Q : Nat) (i : Fin (dbonacci d (Q + 2) - 1)) :
    Fin (dbonacci d (Q + 2)) :=
  ⟨i.1 + 1, by have := i.2; omega⟩

theorem gapLeft_lt_gapRight (d Q : Nat) (i : Fin (dbonacci d (Q + 2) - 1)) :
    gapLeft d Q i < gapRight d Q i := by
  simp [gapLeft, gapRight]

/-- Fine indices strictly between the embedded endpoints of one coarse gap. -/
noncomputable def insertedNameIndices (d Q : Nat)
    (i : Fin (dbonacci d (Q + 2) - 1)) : Finset (Fin (dbonacci d (Q + 3))) :=
  Finset.Ioo (levelEmbedding d Q (gapLeft d Q i))
    (levelEmbedding d Q (gapRight d Q i))

theorem mem_insertedNameIndices_iff (d Q : Nat) (hd : 2 ≤ d)
    (i : Fin (dbonacci d (Q + 2) - 1)) (j : Fin (dbonacci d (Q + 3))) :
    j ∈ insertedNameIndices d Q i ↔
      indexedNameValue d Q (gapLeft d Q i) < indexedNameValue d (Q + 1) j ∧
        indexedNameValue d (Q + 1) j < indexedNameValue d Q (gapRight d Q i) := by
  rw [insertedNameIndices, Finset.mem_Ioo]
  rw [← (indexed_nameValue_strictMono d (Q + 1) hd).lt_iff_lt,
    ← (indexed_nameValue_strictMono d (Q + 1) hd).lt_iff_lt]
  simp only [levelEmbedding_value]

/-- The weight of the newly available final digit at refinement `Q` to `Q+1`. -/
noncomputable def newDigitWeight (d Q : Nat) : Real :=
  (dbonacciPerronRoot d)⁻¹ ^ (Q + 1)

/-- The coarse index obtained by deleting a fine name's final digit. -/
noncomputable def truncationIndex (d Q : Nat) (j : Fin (dbonacci d (Q + 3))) :
    Fin (dbonacci d (Q + 2)) :=
  (dbonacciIndexEquiv d Q).symm
    (truncatedName d Q (dbonacciIndexEquiv d (Q + 1) j))

theorem indexedNameValue_truncation (d Q : Nat)
    (j : Fin (dbonacci d (Q + 3))) :
    indexedNameValue d (Q + 1) j =
      indexedNameValue d Q (truncationIndex d Q j) +
        (if (dbonacciIndexEquiv d (Q + 1) j).1 (Fin.last Q) then
          newDigitWeight d Q else 0) := by
  change dbonacciNameValue d (Q + 1) (dbonacciIndexEquiv d (Q + 1) j) =
    dbonacciNameValue d Q
        (dbonacciIndexEquiv d Q
          ((dbonacciIndexEquiv d Q).symm
            (truncatedName d Q (dbonacciIndexEquiv d (Q + 1) j)))) + _
  rw [(dbonacciIndexEquiv d Q).apply_symm_apply]
  exact truncatedName_value d Q (dbonacciIndexEquiv d (Q + 1) j)

theorem indexedNameValue_truncation_le (d Q : Nat) (hd : 2 ≤ d)
    (j : Fin (dbonacci d (Q + 3))) :
    indexedNameValue d Q (truncationIndex d Q j) ≤
      indexedNameValue d (Q + 1) j := by
  have hvalue := indexedNameValue_truncation d Q j
  by_cases hlast : (dbonacciIndexEquiv d (Q + 1) j).1 (Fin.last Q)
  · rw [if_pos hlast] at hvalue
    have hpositive : 0 < newDigitWeight d Q :=
      pow_pos (dbonacci_root_inv_pos d hd) _
    linarith
  · rw [if_neg hlast] at hvalue
    linarith

theorem indexedNameValue_le_truncation_add (d Q : Nat) (hd : 2 ≤ d)
    (j : Fin (dbonacci d (Q + 3))) :
    indexedNameValue d (Q + 1) j ≤
      indexedNameValue d Q (truncationIndex d Q j) + newDigitWeight d Q := by
  have hvalue := indexedNameValue_truncation d Q j
  by_cases hlast : (dbonacciIndexEquiv d (Q + 1) j).1 (Fin.last Q)
  · rw [if_pos hlast] at hvalue
    linarith
  · rw [if_neg hlast] at hvalue
    have hpositive : 0 < newDigitWeight d Q :=
      pow_pos (dbonacci_root_inv_pos d hd) _
    linarith

theorem root_inv_le_budget (d fuel : Nat) (hd : 2 ≤ d) :
    (dbonacciPerronRoot d)⁻¹ ≤ dbonacciBudgetBound d fuel := by
  induction fuel with
  | zero => simp [dbonacciBudgetBound]
  | succ fuel ih =>
      rw [dbonacciBudgetBound_succ_add]
      exact le_trans ih (le_add_of_nonneg_right
        (pow_nonneg (dbonacci_root_inv_pos d hd).le _))

/-- The zero label is one new top-label gap after refinement. -/
theorem gapLength_zero_substitution (d Q : Nat) (hd : 2 ≤ d) :
    dbonacciGapLength d Q 0 = dbonacciGapLength d (Q + 1) (d - 1) := by
  unfold dbonacciGapLength
  rw [show dbonacciBudgetBound d 0 = (dbonacciPerronRoot d)⁻¹ by
      simp [dbonacciBudgetBound],
    dbonacciBudgetBound_full d hd, mul_one, pow_succ]

/-- A positive label splits into the new top label followed by its predecessor. -/
theorem gapLength_succ_substitution (d Q fuel : Nat) (hd : 2 ≤ d) :
    dbonacciGapLength d Q (fuel + 1) =
      dbonacciGapLength d (Q + 1) (d - 1) +
        dbonacciGapLength d (Q + 1) fuel := by
  unfold dbonacciGapLength
  rw [dbonacciBudgetBound_succ, dbonacciBudgetBound_full d hd, pow_succ]
  ring

theorem newDigitWeight_eq_topGap (d Q : Nat) (hd : 2 ≤ d) :
    newDigitWeight d Q = dbonacciGapLength d (Q + 1) (d - 1) := by
  unfold newDigitWeight dbonacciGapLength
  rw [dbonacciBudgetBound_full d hd, mul_one]

theorem coarse_gap_lower_bound (d Q : Nat) (hd : 2 ≤ d)
    (i : Fin (dbonacci d (Q + 2) - 1)) :
    newDigitWeight d Q ≤
      indexedNameValue d Q (gapRight d Q i) -
        indexedNameValue d Q (gapLeft d Q i) := by
  obtain ⟨label, _, hgap⟩ := consecutive_nameValue_gap d Q hd i
  change indexedNameValue d Q (gapRight d Q i) -
      indexedNameValue d Q (gapLeft d Q i) = dbonacciGapLength d Q label at hgap
  rw [hgap]
  unfold newDigitWeight dbonacciGapLength
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_left (root_inv_le_budget d label hd)
    (pow_nonneg (dbonacci_root_inv_pos d hd).le _)

theorem indexedNameValue_add_newDigit_le (d Q : Nat) (hd : 2 ≤ d)
    (a b : Fin (dbonacci d (Q + 2))) (hab : a < b) :
    indexedNameValue d Q a + newDigitWeight d Q ≤ indexedNameValue d Q b := by
  let step : Fin (dbonacci d (Q + 2) - 1) := ⟨a.1, by
    have hb := b.2
    omega⟩
  have hgap := coarse_gap_lower_bound d Q hd step
  have hleft : gapLeft d Q step = a := by
    apply Fin.ext
    rfl
  let next : Fin (dbonacci d (Q + 2)) := ⟨a.1 + 1, by
    have hb := b.2
    omega⟩
  have hright : gapRight d Q step = next := by
    apply Fin.ext
    rfl
  have hnextle : next ≤ b := by
    change a.1 + 1 ≤ b.1
    exact hab
  have hmono := (indexed_nameValue_strictMono d Q hd).monotone hnextle
  rw [hleft, hright] at hgap
  linarith

/-- Every fine value inside a coarse gap is exactly one new-digit weight from the left. -/
theorem insertedNameValue_eq (d Q : Nat) (hd : 2 ≤ d)
    (i : Fin (dbonacci d (Q + 2) - 1)) (j : Fin (dbonacci d (Q + 3)))
    (hj : j ∈ insertedNameIndices d Q i) :
    indexedNameValue d (Q + 1) j =
      indexedNameValue d Q (gapLeft d Q i) + newDigitWeight d Q := by
  have hjbounds := (mem_insertedNameIndices_iff d Q hd i j).1 hj
  let k := truncationIndex d Q j
  have hnotBefore : ¬ k < gapLeft d Q i := by
    intro hk
    have hstep := indexedNameValue_add_newDigit_le d Q hd k (gapLeft d Q i) hk
    have hfine := indexedNameValue_le_truncation_add d Q hd j
    change indexedNameValue d Q k + newDigitWeight d Q ≤
      indexedNameValue d Q (gapLeft d Q i) at hstep
    change indexedNameValue d (Q + 1) j ≤
      indexedNameValue d Q k + newDigitWeight d Q at hfine
    linarith
  have hnotAfter : ¬ gapLeft d Q i < k := by
    intro hk
    have hrightle : gapRight d Q i ≤ k := by
      change i.1 + 1 ≤ k.1
      change i.1 < k.1 at hk
      omega
    have hmono := (indexed_nameValue_strictMono d Q hd).monotone hrightle
    have htrunc := indexedNameValue_truncation_le d Q hd j
    change indexedNameValue d Q (gapRight d Q i) ≤ indexedNameValue d Q k at hmono
    change indexedNameValue d Q k ≤ indexedNameValue d (Q + 1) j at htrunc
    linarith
  have hk : k = gapLeft d Q i :=
    le_antisymm (le_of_not_gt hnotAfter) (le_of_not_gt hnotBefore)
  have hvalue := indexedNameValue_truncation d Q j
  change indexedNameValue d (Q + 1) j = indexedNameValue d Q k + _ at hvalue
  rw [hk] at hvalue
  by_cases hlast : (dbonacciIndexEquiv d (Q + 1) j).1 (Fin.last Q)
  · simpa [hlast] using hvalue
  · rw [if_neg hlast] at hvalue
    exfalso
    have hpositive : 0 < newDigitWeight d Q :=
      pow_pos (dbonacci_root_inv_pos d hd) _
    linarith

theorem insertedNameIndices_card_le_one (d Q : Nat) (hd : 2 ≤ d)
    (i : Fin (dbonacci d (Q + 2) - 1)) :
    (insertedNameIndices d Q i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  apply (indexed_nameValue_strictMono d (Q + 1) hd).injective
  rw [insertedNameValue_eq d Q hd i a ha, insertedNameValue_eq d Q hd i b hb]

theorem zero_gap_no_insertion (d Q : Nat) (hd : 2 ≤ d)
    (i : Fin (dbonacci d (Q + 2) - 1))
    (hzero :
      indexedNameValue d Q (gapRight d Q i) - indexedNameValue d Q (gapLeft d Q i) =
        dbonacciGapLength d Q 0) :
    insertedNameIndices d Q i = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have hvalue := insertedNameValue_eq d Q hd i j hj
  have hbounds := (mem_insertedNameIndices_iff d Q hd i j).1 hj
  have hweight : dbonacciGapLength d Q 0 = newDigitWeight d Q := by
    rw [gapLength_zero_substitution d Q hd]
    exact (newDigitWeight_eq_topGap d Q hd).symm
  linarith

/-- Predicate that a real length is one of the exact level-`Q` d-bonacci gaps. -/
def IsDBonacciGap (d Q : Nat) (length : Real) : Prop :=
  ∃ label ∈ Finset.Ico (d - Q) d, length = dbonacciGapLength d Q label

/-- With no inserted name, an embedded coarse interval is one fine adjacent gap. -/
theorem coarse_gap_is_fine_of_no_insertion (d Q : Nat) (hd : 2 ≤ d)
    (i : Fin (dbonacci d (Q + 2) - 1))
    (hempty : insertedNameIndices d Q i = ∅) :
    IsDBonacciGap d (Q + 1)
      (indexedNameValue d Q (gapRight d Q i) -
        indexedNameValue d Q (gapLeft d Q i)) := by
  have hembedded :
      levelEmbedding d Q (gapLeft d Q i) < levelEmbedding d Q (gapRight d Q i) :=
    levelEmbedding_strictMono d Q hd (gapLeft_lt_gapRight d Q i)
  have hcard : (insertedNameIndices d Q i).card = 0 := by
    rw [hempty]
    rfl
  rw [insertedNameIndices, Fin.card_Ioo] at hcard
  have hsucc :
      (levelEmbedding d Q (gapRight d Q i)).1 =
        (levelEmbedding d Q (gapLeft d Q i)).1 + 1 := by
    change (levelEmbedding d Q (gapLeft d Q i)).1 <
      (levelEmbedding d Q (gapRight d Q i)).1 at hembedded
    omega
  let step : Fin (dbonacci d (Q + 3) - 1) :=
    ⟨(levelEmbedding d Q (gapLeft d Q i)).1, by
      have hright := (levelEmbedding d Q (gapRight d Q i)).2
      omega⟩
  obtain ⟨label, hlabel, hgap⟩ := consecutive_nameValue_gap d (Q + 1) hd step
  refine ⟨label, hlabel, ?_⟩
  have hleft :
      (⟨step.1, by
        have := step.2
        have hpos := dbonacci_level_pos d (Q + 1) (by omega)
        omega⟩ : Fin (dbonacci d (Q + 3))) =
        levelEmbedding d Q (gapLeft d Q i) := by
    apply Fin.ext
    rfl
  have hright :
      (⟨step.1 + 1, by
        have := step.2
        have hpos := dbonacci_level_pos d (Q + 1) (by omega)
        omega⟩ : Fin (dbonacci d (Q + 3))) =
        levelEmbedding d Q (gapRight d Q i) := by
    apply Fin.ext
    exact hsucc.symm
  rw [hleft, hright, levelEmbedding_value, levelEmbedding_value] at hgap
  exact hgap

theorem succ_gap_not_fine (d Q fuel : Nat) (hd : 2 ≤ d) :
    ¬ IsDBonacciGap d (Q + 1) (dbonacciGapLength d Q (fuel + 1)) := by
  rintro ⟨label, hlabel, heq⟩
  have hlabelLt : label < d := (Finset.mem_Ico.mp hlabel).2
  have hlabelLe : label ≤ d - 1 := by omega
  have hmax := (dbonacciGapLength_strictMono d (Q + 1) hd).monotone hlabelLe
  have hsplit := gapLength_succ_substitution d Q fuel hd
  have hpositive := dbonacciGapLength_pos d (Q + 1) fuel hd
  linarith

theorem succ_gap_insertion_count (d Q fuel : Nat) (hd : 2 ≤ d)
    (i : Fin (dbonacci d (Q + 2) - 1))
    (hgap :
      indexedNameValue d Q (gapRight d Q i) - indexedNameValue d Q (gapLeft d Q i) =
        dbonacciGapLength d Q (fuel + 1)) :
    (insertedNameIndices d Q i).card = 1 := by
  have hne : insertedNameIndices d Q i ≠ ∅ := by
    intro hempty
    apply succ_gap_not_fine d Q fuel hd
    rw [← hgap]
    exact coarse_gap_is_fine_of_no_insertion d Q hd i hempty
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hle := insertedNameIndices_card_le_one d Q hd i
  have hpos : 0 < (insertedNameIndices d Q i).card := Finset.card_pos.mpr ⟨j, hj⟩
  omega

/-- Every coarse gap realizes `0 -> [d-1]` or `f+1 -> [d-1,f]` at the fine level. -/
theorem dbonacci_gap_substitution (d Q : Nat) (hd : 2 ≤ d)
    (i : Fin (dbonacci d (Q + 2) - 1)) :
    ∃ label ∈ Finset.Ico (d - Q) d,
      indexedNameValue d Q (gapRight d Q i) - indexedNameValue d Q (gapLeft d Q i) =
          dbonacciGapLength d Q label ∧
        match label with
        | 0 =>
            insertedNameIndices d Q i = ∅ ∧
              indexedNameValue d (Q + 1) (levelEmbedding d Q (gapRight d Q i)) -
                  indexedNameValue d (Q + 1) (levelEmbedding d Q (gapLeft d Q i)) =
                dbonacciGapLength d (Q + 1) (d - 1)
        | fuel + 1 =>
            ∃ j : Fin (dbonacci d (Q + 3)),
              insertedNameIndices d Q i = {j} ∧
                indexedNameValue d (Q + 1) j -
                    indexedNameValue d Q (gapLeft d Q i) =
                  dbonacciGapLength d (Q + 1) (d - 1) ∧
                indexedNameValue d Q (gapRight d Q i) -
                    indexedNameValue d (Q + 1) j =
                  dbonacciGapLength d (Q + 1) fuel := by
  obtain ⟨label, hlabel, hgap⟩ := consecutive_nameValue_gap d Q hd i
  change indexedNameValue d Q (gapRight d Q i) -
      indexedNameValue d Q (gapLeft d Q i) = dbonacciGapLength d Q label at hgap
  refine ⟨label, hlabel, hgap, ?_⟩
  cases label with
  | zero =>
      constructor
      · exact zero_gap_no_insertion d Q hd i hgap
      · rw [levelEmbedding_value, levelEmbedding_value, hgap]
        exact gapLength_zero_substitution d Q hd
  | succ fuel =>
      obtain ⟨j, hset⟩ := Finset.card_eq_one.mp
        (succ_gap_insertion_count d Q fuel hd i hgap)
      have hj : j ∈ insertedNameIndices d Q i := by
        rw [hset]
        simp
      have hvalue := insertedNameValue_eq d Q hd i j hj
      have htop := newDigitWeight_eq_topGap d Q hd
      have hsplit := gapLength_succ_substitution d Q fuel hd
      refine ⟨j, hset, ?_, ?_⟩
      · linarith
      · linarith

/-- The measured gap-label replacement suggested by the finite tables. -/
def gapLabelSubstitution (d : Nat) : Nat -> List Nat
  | 0 => [d - 1]
  | fuel + 1 => [d - 1, fuel]

/-- The general and frozen order-three embeddings adjoin the same final digit. -/
theorem extendedName_three_word_eq_tribonacci (Q : Nat)
    (dname : DBonacciName 3 Q)
    (tname : D5.S0.Tower.Tribonacci.Names.TribonacciName Q)
    (hword : dname.1 = tname.1) :
    (extendedName 3 Q dname).1 =
      (D5.S0.Tower.Tribonacci.Substitution.extendedName Q tname).1 := by
  change (Fin.snoc dname.1 false : Fin (Q + 1) -> Bool) =
    (Fin.snoc tname.1 false : Fin (Q + 1) -> Bool)
  rw [hword]

/-- Explicit identification of general order-three labels with the frozen alphabet. -/
def tribonacciGapLetterOfLabel : Nat ->
    D5.S0.Tower.Tribonacci.Substitution.TribonacciGapLetter
  | 0 => .small
  | 1 => .combined
  | _ => .large

/-- Pointwise compatibility with the frozen Tribonacci substitution, not a second source. -/
theorem gapLabelSubstitution_three_compatible (label : Fin 3) :
    (gapLabelSubstitution 3 label.1).map tribonacciGapLetterOfLabel =
      D5.S0.Tower.Tribonacci.Substitution.gapLetterSubstitution
        (tribonacciGapLetterOfLabel label.1) := by
  fin_cases label <;>
    norm_num [gapLabelSubstitution, tribonacciGapLetterOfLabel,
      D5.S0.Tower.Tribonacci.Substitution.gapLetterSubstitution]

/-- The digit of an encoded word at a zero-based position from the right. -/
def codeDigit (code position : Nat) : Bool :=
  code / 2 ^ position % 2 == 1

/-- Executable run-budget scan of an encoded word, from its most significant digit. -/
def codeRunAdmissible (maxTrue : Nat) : (fuel Q code : Nat) -> Bool
  | _, 0, _ => true
  | 0, q + 1, code =>
      if codeDigit code q then false else codeRunAdmissible maxTrue maxTrue q code
  | fuel + 1, q + 1, code =>
      if codeDigit code q then
        codeRunAdmissible maxTrue fuel q code
      else
        codeRunAdmissible maxTrue maxTrue q code

theorem codeRunAdmissible_eq_runAdmissible (maxTrue fuel Q code : Nat) :
    codeRunAdmissible maxTrue fuel Q code =
      runAdmissible maxTrue fuel Q fun i => codeDigit code (Q - 1 - i.1) := by
  induction Q generalizing fuel with
  | zero => simp [codeRunAdmissible, runAdmissible]
  | succ Q ih =>
      have hhead : codeDigit code (Q + 1 - 1 - (0 : Fin (Q + 1)).1) =
          codeDigit code Q := by
        simp
      have htail :
          Fin.tail (fun i : Fin (Q + 1) => codeDigit code (Q + 1 - 1 - i.1)) =
            (fun i : Fin Q => codeDigit code (Q - 1 - i.1)) := by
        funext i
        simp only [Fin.tail, Fin.val_succ]
        congr 1
        omega
      cases fuel with
      | zero =>
          rw [codeRunAdmissible, runAdmissible, hhead, htail]
          by_cases hbit : codeDigit code Q <;> simp [hbit, ih]
      | succ fuel =>
          rw [codeRunAdmissible, runAdmissible, hhead, htail]
          by_cases hbit : codeDigit code Q <;> simp [hbit, ih]

/-- Boolean form of admissibility for an encoded word. -/
def codeAdmissible (d Q code : Nat) : Bool :=
  match d with
  | 0 => false
  | maxTrue + 1 =>
      codeRunAdmissible maxTrue maxTrue Q code

theorem codeAdmissible_iff (d Q code : Nat) :
    codeAdmissible d Q code = true ↔
      DBonacciAdmissible d Q fun i => codeDigit code (Q - 1 - i.1) := by
  cases d with
  | zero => simp [codeAdmissible, DBonacciAdmissible]
  | succ maxTrue =>
      simp only [codeAdmissible, DBonacciAdmissible]
      rw [codeRunAdmissible_eq_runAdmissible]

/-- Admissible words encoded in executable prefix order, with the first digit most significant. -/
def admissibleCodeList (d Q : Nat) : List Nat :=
  (List.range (2 ^ Q)).filterMap fun code =>
    match codeAdmissible d Q code with
    | true => some code
    | false => none

/-- Positions of even codes, carrying an explicit scan offset. -/
def evenCodePositions : List Nat -> Nat -> List Nat
  | [], _ => []
  | code :: codes, position =>
      if code % 2 == 0 then
        position :: evenCodePositions codes (position + 1)
      else
        evenCodePositions codes (position + 1)

/-- Measured positions of adjacent coarse words after appending a final false digit. -/
def measuredRefinementIndexTable (d Q : Nat) : List (Nat × Nat) :=
  let positions := evenCodePositions (admissibleCodeList d (Q + 1)) 0
  List.zipWith (fun left right => (left, right)) positions positions.tail

/-- Fine-layer labels cut into the measured intervals between embedded coarse endpoints. -/
def measuredGapSplitTable (d Q : Nat) : List (List Nat) :=
  (measuredRefinementIndexTable d Q).map fun endpoints =>
    ((boundedGapFuelList (d - 1) (d - 1) (Q + 1)).drop endpoints.1).take
      (endpoints.2 - endpoints.1)

theorem admissibleCodeList_three_six : admissibleCodeList 3 6 =
    [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20,
      21, 22, 24, 25, 26, 27, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42,
      43, 44, 45, 48, 49, 50, 51, 52, 53, 54] := by
  norm_num [admissibleCodeList, codeAdmissible, codeRunAdmissible, codeDigit,
    List.range, List.range.loop, List.filterMap]

theorem measuredRefinementIndexTable_three_five :
    measuredRefinementIndexTable 3 5 =
      [(0, 2), (2, 4), (4, 6), (6, 7), (7, 9), (9, 11), (11, 13),
        (13, 15), (15, 17), (17, 19), (19, 20), (20, 22), (22, 24),
        (24, 26), (26, 28), (28, 30), (30, 31), (31, 33), (33, 35),
        (35, 37), (37, 39), (39, 41), (41, 43)] := by
  rw [measuredRefinementIndexTable, admissibleCodeList_three_six]
  norm_num [evenCodePositions, List.zipWith]

theorem admissibleCodeList_four_six : admissibleCodeList 4 6 =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18,
      19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 36,
      37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53,
      54, 55, 56, 57, 58, 59] := by
  norm_num [admissibleCodeList, codeAdmissible, codeRunAdmissible, codeDigit,
    List.range, List.range.loop, List.filterMap]

theorem measuredRefinementIndexTable_four_five :
    measuredRefinementIndexTable 4 5 =
      [(0, 2), (2, 4), (4, 6), (6, 8), (8, 10), (10, 12), (12, 14),
        (14, 15), (15, 17), (17, 19), (19, 21), (21, 23), (23, 25),
        (25, 27), (27, 29), (29, 31), (31, 33), (33, 35), (35, 37),
        (37, 39), (39, 41), (41, 43), (43, 44), (44, 46), (46, 48),
        (48, 50), (50, 52), (52, 54)] := by
  rw [measuredRefinementIndexTable, admissibleCodeList_four_six]
  norm_num [evenCodePositions, List.zipWith]

example : measuredGapSplitTable 2 3 =
    [[1, 0], [1], [1, 0], [1, 0]] := by
  norm_num [measuredGapSplitTable, measuredRefinementIndexTable, admissibleCodeList,
    codeAdmissible, codeRunAdmissible, codeDigit, evenCodePositions,
    boundedGapFuelList, boundedTerminalFuel,
    List.range, List.range.loop, List.filterMap, List.zipWith]

example : measuredGapSplitTable 2 4 =
    [[1, 0], [1], [1, 0], [1, 0], [1], [1, 0], [1]] := by
  norm_num [measuredGapSplitTable, measuredRefinementIndexTable, admissibleCodeList,
    codeAdmissible, codeRunAdmissible, codeDigit, evenCodePositions,
    boundedGapFuelList, boundedTerminalFuel,
    List.range, List.range.loop, List.filterMap, List.zipWith]

example : measuredGapSplitTable 2 5 =
    [[1, 0], [1], [1, 0], [1, 0], [1], [1, 0], [1], [1, 0],
      [1, 0], [1], [1, 0], [1, 0]] := by
  norm_num [measuredGapSplitTable, measuredRefinementIndexTable, admissibleCodeList,
    codeAdmissible, codeRunAdmissible, codeDigit, evenCodePositions,
    boundedGapFuelList, boundedTerminalFuel,
    List.range, List.range.loop, List.filterMap, List.zipWith]

example : measuredGapSplitTable 3 3 =
    [[2, 1], [2, 0], [2, 1], [2], [2, 1], [2, 0]] := by
  norm_num [measuredGapSplitTable, measuredRefinementIndexTable, admissibleCodeList,
    codeAdmissible, codeRunAdmissible, codeDigit, evenCodePositions,
    boundedGapFuelList, boundedTerminalFuel,
    List.range, List.range.loop, List.filterMap, List.zipWith]

example : measuredGapSplitTable 3 4 =
    [[2, 1], [2, 0], [2, 1], [2], [2, 1], [2, 0], [2, 1],
      [2, 1], [2, 0], [2, 1], [2], [2, 1]] := by
  norm_num [measuredGapSplitTable, measuredRefinementIndexTable, admissibleCodeList,
    codeAdmissible, codeRunAdmissible, codeDigit, evenCodePositions,
    boundedGapFuelList, boundedTerminalFuel,
    List.range, List.range.loop, List.filterMap, List.zipWith]

example : measuredGapSplitTable 3 5 =
    [[2, 1], [2, 0], [2, 1], [2], [2, 1], [2, 0], [2, 1],
      [2, 1], [2, 0], [2, 1], [2], [2, 1], [2, 0], [2, 1],
      [2, 0], [2, 1], [2], [2, 1], [2, 0], [2, 1], [2, 1],
      [2, 0], [2, 1]] := by
  rw [measuredGapSplitTable, measuredRefinementIndexTable_three_five]
  norm_num [boundedGapFuelList, boundedTerminalFuel]

example : measuredGapSplitTable 4 3 =
    [[3, 2], [3, 1], [3, 2], [3, 0], [3, 2], [3, 1], [3, 2]] := by
  norm_num [measuredGapSplitTable, measuredRefinementIndexTable, admissibleCodeList,
    codeAdmissible, codeRunAdmissible, codeDigit, evenCodePositions,
    boundedGapFuelList, boundedTerminalFuel,
    List.range, List.range.loop, List.filterMap, List.zipWith]

example : measuredGapSplitTable 4 4 =
    [[3, 2], [3, 1], [3, 2], [3, 0], [3, 2], [3, 1], [3, 2],
      [3], [3, 2], [3, 1], [3, 2], [3, 0], [3, 2], [3, 1]] := by
  norm_num [measuredGapSplitTable, measuredRefinementIndexTable, admissibleCodeList,
    codeAdmissible, codeRunAdmissible, codeDigit, evenCodePositions,
    boundedGapFuelList, boundedTerminalFuel,
    List.range, List.range.loop, List.filterMap, List.zipWith]

example : measuredGapSplitTable 4 5 =
    [[3, 2], [3, 1], [3, 2], [3, 0], [3, 2], [3, 1], [3, 2],
      [3], [3, 2], [3, 1], [3, 2], [3, 0], [3, 2], [3, 1],
      [3, 2], [3, 2], [3, 1], [3, 2], [3, 0], [3, 2], [3, 1],
      [3, 2], [3], [3, 2], [3, 1], [3, 2], [3, 0], [3, 2]] := by
  rw [measuredGapSplitTable, measuredRefinementIndexTable_four_five]
  norm_num [boundedGapFuelList, boundedTerminalFuel]

end D5.S0.Tower.DBonacci.Substitution

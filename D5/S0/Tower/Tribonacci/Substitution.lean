/- GID: D5/S0/Tower/Tribonacci/Substitution
   generality: I
   mirror-B: D5/B/S0/Tower/Tribonacci/Substitution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refining Tribonacci gaps realizes a three-letter substitution. -/

import D5.S0.Tower.Tribonacci.Gaps
import Mathlib.Order.Interval.Finset.Fin

namespace D5.S0.Tower.Tribonacci.Substitution

open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Values
open D5.S0.Tower.Tribonacci.Gaps

local notation "t" => tribonacciConstant

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

theorem admissible_snoc_false (Q : Nat) (word : Fin Q -> Bool)
    (hadmissible : TribonacciAdmissible Q word) :
    TribonacciAdmissible (Q + 1) (Fin.snoc word false) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      match Q with
      | 0 => trivial
      | 1 => trivial
      | 2 =>
          rw [admissible_add_three_iff 0]
          constructor
          · intro hbad
            have hlast :
                (Fin.snoc word false : Fin 3 -> Bool) (2 : Fin 3) = false := by
              rw [show (2 : Fin 3) = Fin.last 2 by decide, Fin.snoc_last]
            simp [hlast] at hbad
          · trivial
      | n + 3 =>
          rw [admissible_add_three_iff (n + 1)]
          have hsource := (admissible_add_three_iff n word).1 hadmissible
          constructor
          · simpa only [show (0 : Fin (n + 4)) = (0 : Fin (n + 3)).castSucc by
                apply Fin.ext; rfl,
              show (1 : Fin (n + 4)) = (1 : Fin (n + 3)).castSucc by
                apply Fin.ext; rfl,
              show (2 : Fin (n + 4)) = (2 : Fin (n + 3)).castSucc by
                apply Fin.ext; rfl,
              Fin.snoc_castSucc] using hsource.1
          · rw [tail_snoc_false (n + 2) word]
            exact ih (n + 2) (by omega) (Fin.tail word) hsource.2

theorem admissible_init (Q : Nat) (word : Fin (Q + 1) -> Bool)
    (hadmissible : TribonacciAdmissible (Q + 1) word) :
    TribonacciAdmissible Q (Fin.init word) := by
  induction Q using Nat.strong_induction_on with
  | h Q ih =>
      match Q with
      | 0 => trivial
      | 1 => trivial
      | 2 => trivial
      | n + 3 =>
          rw [admissible_add_three_iff n]
          have hsource := (admissible_add_three_iff (n + 1) word).1 hadmissible
          constructor
          · simpa only [Fin.init,
                show (0 : Fin (n + 3)).castSucc = (0 : Fin (n + 4)) by
                  apply Fin.ext; rfl,
                show (1 : Fin (n + 3)).castSucc = (1 : Fin (n + 4)) by
                  apply Fin.ext; rfl,
                show (2 : Fin (n + 3)).castSucc = (2 : Fin (n + 4)) by
                  apply Fin.ext; rfl] using hsource.1
          · rw [show Fin.tail (Fin.init word) = Fin.init (Fin.tail word) by
                funext i
                rfl]
            exact ih (n + 2) (by omega) (Fin.tail word) hsource.2

theorem tribonacciWordValue_snoc (Q : Nat) (word : Fin Q -> Bool) (last : Bool) :
    tribonacciWordValue (Q + 1) (Fin.snoc word last) =
      tribonacciWordValue Q word +
        (if last then t ^ (-((Q + 1 : Nat) : Int)) else 0) := by
  unfold tribonacciWordValue
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]

/-- A level-`Q` name, extended by a final zero at level `Q+1`. -/
def extendedName (Q : Nat) (name : TribonacciName Q) : TribonacciName (Q + 1) :=
  ⟨Fin.snoc name.1 false, admissible_snoc_false Q name.1 name.2⟩

/-- A fine name with its final digit removed. -/
def truncatedName (Q : Nat) (name : TribonacciName (Q + 1)) : TribonacciName Q :=
  ⟨Fin.init name.1, admissible_init Q name.1 name.2⟩

theorem extendedName_value (Q : Nat) (name : TribonacciName Q) :
    tribonacciNameValue (Q + 1) (extendedName Q name) =
      tribonacciNameValue Q name := by
  rw [tribonacciNameValue, tribonacciNameValue]
  change tribonacciWordValue (Q + 1) (Fin.snoc name.1 false) =
    tribonacciWordValue Q name.1
  rw [tribonacciWordValue_snoc]
  simp

theorem truncatedName_value (Q : Nat) (name : TribonacciName (Q + 1)) :
    tribonacciNameValue (Q + 1) name =
      tribonacciNameValue Q (truncatedName Q name) +
        (if name.1 (Fin.last Q) then t ^ (-((Q + 1 : Nat) : Int)) else 0) := by
  rw [tribonacciNameValue, tribonacciNameValue]
  change tribonacciWordValue (Q + 1) name.1 =
    tribonacciWordValue Q (Fin.init name.1) + _
  conv_lhs => rw [← Fin.snoc_init_self name.1]
  exact tribonacciWordValue_snoc Q (Fin.init name.1) (name.1 (Fin.last Q))

/-- The index at level `Q+1` of a level-`Q` name with the same value. -/
def levelEmbedding (Q : Nat) (i : Fin (tribonacci (Q + 2))) :
    Fin (tribonacci (Q + 3)) :=
  (tribonacciIndexEquiv (Q + 1)).symm (extendedName Q (tribonacciIndexEquiv Q i))

theorem levelEmbedding_value (Q : Nat) (i : Fin (tribonacci (Q + 2))) :
    indexedNameValue (Q + 1) (levelEmbedding Q i) = indexedNameValue Q i := by
  change tribonacciNameValue (Q + 1)
      (tribonacciIndexEquiv (Q + 1)
        ((tribonacciIndexEquiv (Q + 1)).symm
          (extendedName Q (tribonacciIndexEquiv Q i)))) =
    tribonacciNameValue Q (tribonacciIndexEquiv Q i)
  rw [(tribonacciIndexEquiv (Q + 1)).apply_symm_apply]
  exact extendedName_value Q (tribonacciIndexEquiv Q i)

theorem levelEmbedding_strictMono (Q : Nat) : StrictMono (levelEmbedding Q) := by
  intro i j hij
  apply ((indexed_nameValue_strictMono (Q + 1)).lt_iff_lt).mp
  rw [levelEmbedding_value, levelEmbedding_value]
  exact indexed_nameValue_strictMono Q hij

/-- The left endpoint of a coarse adjacent gap. -/
def gapLeft (Q : Nat) (i : Fin (tribonacci (Q + 2) - 1)) :
    Fin (tribonacci (Q + 2)) :=
  ⟨i.1, by have := i.2; have := tribonacci_level_pos Q; omega⟩

/-- The right endpoint of a coarse adjacent gap. -/
def gapRight (Q : Nat) (i : Fin (tribonacci (Q + 2) - 1)) :
    Fin (tribonacci (Q + 2)) :=
  ⟨i.1 + 1, by have := i.2; have := tribonacci_level_pos Q; omega⟩

theorem gapLeft_lt_gapRight (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1)) : gapLeft Q i < gapRight Q i := by
  simp [gapLeft, gapRight]

/-- Fine-level indices strictly between the embedded endpoints of a coarse gap. -/
def insertedNameIndices (Q : Nat) (i : Fin (tribonacci (Q + 2) - 1)) :
    Finset (Fin (tribonacci (Q + 3))) :=
  Finset.Ioo (levelEmbedding Q (gapLeft Q i)) (levelEmbedding Q (gapRight Q i))

theorem mem_insertedNameIndices_iff (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1)) (j : Fin (tribonacci (Q + 3))) :
    j ∈ insertedNameIndices Q i ↔
      indexedNameValue Q (gapLeft Q i) < indexedNameValue (Q + 1) j ∧
        indexedNameValue (Q + 1) j < indexedNameValue Q (gapRight Q i) := by
  rw [insertedNameIndices, Finset.mem_Ioo]
  rw [← (indexed_nameValue_strictMono (Q + 1)).lt_iff_lt,
    ← (indexed_nameValue_strictMono (Q + 1)).lt_iff_lt]
  simp only [levelEmbedding_value]

/-- The coarse index obtained by deleting a fine name's final digit. -/
def truncationIndex (Q : Nat) (j : Fin (tribonacci (Q + 3))) :
    Fin (tribonacci (Q + 2)) :=
  (tribonacciIndexEquiv Q).symm (truncatedName Q (tribonacciIndexEquiv (Q + 1) j))

theorem indexedNameValue_truncation (Q : Nat) (j : Fin (tribonacci (Q + 3))) :
    indexedNameValue (Q + 1) j =
      indexedNameValue Q (truncationIndex Q j) +
        (if (tribonacciIndexEquiv (Q + 1) j).1 (Fin.last Q) then
          t ^ (-((Q + 1 : Nat) : Int)) else 0) := by
  change tribonacciNameValue (Q + 1) (tribonacciIndexEquiv (Q + 1) j) =
    tribonacciNameValue Q
        (tribonacciIndexEquiv Q
          ((tribonacciIndexEquiv Q).symm
            (truncatedName Q (tribonacciIndexEquiv (Q + 1) j)))) + _
  rw [(tribonacciIndexEquiv Q).apply_symm_apply]
  exact truncatedName_value Q (tribonacciIndexEquiv (Q + 1) j)

theorem indexedNameValue_truncation_le (Q : Nat)
    (j : Fin (tribonacci (Q + 3))) :
    indexedNameValue Q (truncationIndex Q j) ≤ indexedNameValue (Q + 1) j := by
  have hvalue := indexedNameValue_truncation Q j
  by_cases hlast : (tribonacciIndexEquiv (Q + 1) j).1 (Fin.last Q)
  · rw [if_pos hlast] at hvalue
    nlinarith [zpow_pos tribonacciConstant_pos (-((Q + 1 : Nat) : Int))]
  · rw [if_neg hlast] at hvalue
    linarith

theorem indexedNameValue_le_truncation_add (Q : Nat)
    (j : Fin (tribonacci (Q + 3))) :
    indexedNameValue (Q + 1) j ≤
      indexedNameValue Q (truncationIndex Q j) +
        t ^ (-((Q + 1 : Nat) : Int)) := by
  have hvalue := indexedNameValue_truncation Q j
  by_cases hlast : (tribonacciIndexEquiv (Q + 1) j).1 (Fin.last Q)
  · rw [if_pos hlast] at hvalue
    linarith
  · rw [if_neg hlast] at hvalue
    nlinarith [zpow_pos tribonacciConstant_pos (-((Q + 1 : Nat) : Int))]

theorem coarse_gap_lower_bound (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1)) :
    t ^ (-((Q + 1 : Nat) : Int)) ≤
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) := by
  have hnextOne : 0 < t ^ (-((Q + 1 : Nat) : Int)) :=
    zpow_pos tribonacciConstant_pos _
  have hnextTwo : 0 < t ^ (-((Q + 2 : Nat) : Int)) :=
    zpow_pos tribonacciConstant_pos _
  have hnextThree : 0 < t ^ (-((Q + 3 : Nat) : Int)) :=
    zpow_pos tribonacciConstant_pos _
  have hrec := tribonacci_zpow_recurrence Q
  rcases consecutive_nameValue_gap Q i with hlarge | hsmall | hcombined
  · change indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
      t ^ (-(Q : Int)) at hlarge
    rw [hlarge]
    linarith
  · change indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
      t ^ (-((Q + 1 : Nat) : Int)) at hsmall
    rw [hsmall]
  · change indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
      t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int)) at hcombined
    rw [hcombined]
    linarith

theorem indexedNameValue_add_fine_large_le (Q : Nat)
    (a b : Fin (tribonacci (Q + 2))) (hab : a < b) :
    indexedNameValue Q a + t ^ (-((Q + 1 : Nat) : Int)) ≤
      indexedNameValue Q b := by
  let step : Fin (tribonacci (Q + 2) - 1) := ⟨a.1, by
    have hb := b.2
    have hpos := tribonacci_level_pos Q
    omega⟩
  have hgap := coarse_gap_lower_bound Q step
  have hleft : gapLeft Q step = a := by
    apply Fin.ext
    rfl
  let next : Fin (tribonacci (Q + 2)) := ⟨a.1 + 1, by
    have hb := b.2
    omega⟩
  have hright : gapRight Q step = next := by
    apply Fin.ext
    rfl
  have hnextle : next ≤ b := by
    change a.1 + 1 ≤ b.1
    exact hab
  have hmono := (indexed_nameValue_strictMono Q).monotone hnextle
  rw [hleft, hright] at hgap
  linarith

/-- Every inserted fine value is the coarse left endpoint plus the new large length. -/
theorem insertedNameValue_eq (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1)) (j : Fin (tribonacci (Q + 3)))
    (hj : j ∈ insertedNameIndices Q i) :
    indexedNameValue (Q + 1) j =
      indexedNameValue Q (gapLeft Q i) + t ^ (-((Q + 1 : Nat) : Int)) := by
  have hjbounds := (mem_insertedNameIndices_iff Q i j).1 hj
  let k := truncationIndex Q j
  have hnotBefore : ¬ k < gapLeft Q i := by
    intro hk
    have hstep := indexedNameValue_add_fine_large_le Q k (gapLeft Q i) hk
    have hfine := indexedNameValue_le_truncation_add Q j
    change indexedNameValue Q k + t ^ (-((Q + 1 : Nat) : Int)) ≤
      indexedNameValue Q (gapLeft Q i) at hstep
    change indexedNameValue (Q + 1) j ≤
      indexedNameValue Q k + t ^ (-((Q + 1 : Nat) : Int)) at hfine
    linarith
  have hnotAfter : ¬ gapLeft Q i < k := by
    intro hk
    have hrightle : gapRight Q i ≤ k := by
      change i.1 + 1 ≤ k.1
      change i.1 < k.1 at hk
      omega
    have hmono := (indexed_nameValue_strictMono Q).monotone hrightle
    have htrunc := indexedNameValue_truncation_le Q j
    change indexedNameValue Q (gapRight Q i) ≤ indexedNameValue Q k at hmono
    change indexedNameValue Q k ≤ indexedNameValue (Q + 1) j at htrunc
    linarith
  have hk : k = gapLeft Q i := le_antisymm (le_of_not_gt hnotAfter) (le_of_not_gt hnotBefore)
  have hvalue := indexedNameValue_truncation Q j
  change indexedNameValue (Q + 1) j = indexedNameValue Q k + _ at hvalue
  rw [hk] at hvalue
  by_cases hlast : (tribonacciIndexEquiv (Q + 1) j).1 (Fin.last Q)
  · simpa [hlast] using hvalue
  · rw [if_neg hlast] at hvalue
    exfalso
    linarith

theorem insertedNameIndices_card_le_one (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1)) :
    (insertedNameIndices Q i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  apply (indexed_nameValue_strictMono (Q + 1)).injective
  rw [insertedNameValue_eq Q i a ha, insertedNameValue_eq Q i b hb]

theorem small_gap_no_insertion (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1))
    (hsmall :
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
        t ^ (-((Q + 1 : Nat) : Int))) :
    insertedNameIndices Q i = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have hvalue := insertedNameValue_eq Q i j hj
  have hbounds := (mem_insertedNameIndices_iff Q i j).1 hj
  linarith

/-- If no name is inserted, the coarse difference is itself a next-level gap. -/
theorem coarse_gap_is_fine_of_no_insertion (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1))
    (hempty : insertedNameIndices Q i = ∅) :
    IsTribonacciGap (Q + 1)
      (indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i)) := by
  have hembedded :
      levelEmbedding Q (gapLeft Q i) < levelEmbedding Q (gapRight Q i) :=
    levelEmbedding_strictMono Q (gapLeft_lt_gapRight Q i)
  have hcard : (insertedNameIndices Q i).card = 0 := by rw [hempty]; rfl
  rw [insertedNameIndices, Fin.card_Ioo] at hcard
  have hsucc :
      (levelEmbedding Q (gapRight Q i)).1 =
        (levelEmbedding Q (gapLeft Q i)).1 + 1 := by
    change (levelEmbedding Q (gapLeft Q i)).1 <
      (levelEmbedding Q (gapRight Q i)).1 at hembedded
    omega
  let step : Fin (tribonacci ((Q + 1) + 2) - 1) :=
    ⟨(levelEmbedding Q (gapLeft Q i)).1, by
      have hright := (levelEmbedding Q (gapRight Q i)).2
      have hpos := tribonacci_level_pos (Q + 1)
      change (levelEmbedding Q (gapLeft Q i)).1 < tribonacci (Q + 3) - 1
      change (levelEmbedding Q (gapRight Q i)).1 < tribonacci (Q + 3) at hright
      omega⟩
  have hgap := consecutive_nameValue_gap (Q + 1) step
  have hleft :
      (⟨step.1, by
        have := step.2
        simp only [Nat.add_assoc, Nat.reduceAdd] at this
        have hpos := tribonacci_level_pos (Q + 1)
        omega⟩ : Fin (tribonacci (Q + 3))) = levelEmbedding Q (gapLeft Q i) := by
    apply Fin.ext
    rfl
  have hright :
      (⟨step.1 + 1, by
        have := step.2
        simp only [Nat.add_assoc, Nat.reduceAdd] at this
        have hpos := tribonacci_level_pos (Q + 1)
        omega⟩ : Fin (tribonacci (Q + 3))) = levelEmbedding Q (gapRight Q i) := by
    apply Fin.ext
    exact hsucc.symm
  change IsTribonacciGap (Q + 1)
    (indexedNameValue (Q + 1)
        ⟨step.1 + 1, by
          have := step.2
          simp only [Nat.add_assoc, Nat.reduceAdd] at this
          have hpos := tribonacci_level_pos (Q + 1)
          omega⟩ -
      indexedNameValue (Q + 1)
        ⟨step.1, by
          have := step.2
          simp only [Nat.add_assoc, Nat.reduceAdd] at this
          have hpos := tribonacci_level_pos (Q + 1)
          omega⟩) at hgap
  rw [hleft, hright, levelEmbedding_value, levelEmbedding_value] at hgap
  exact hgap

theorem large_gap_not_fine (Q : Nat) :
    ¬ IsTribonacciGap (Q + 1) (t ^ (-(Q : Int))) := by
  intro hgap
  have hrec := tribonacci_zpow_recurrence Q
  have hp : 0 < t ^ (-((Q + 1 : Nat) : Int)) := zpow_pos tribonacciConstant_pos _
  have hq : 0 < t ^ (-((Q + 2 : Nat) : Int)) := zpow_pos tribonacciConstant_pos _
  have hr : 0 < t ^ (-((Q + 3 : Nat) : Int)) := zpow_pos tribonacciConstant_pos _
  rcases hgap with hlarge | hsmall | hcombined
  · linarith
  · linarith
  · linarith

theorem combined_gap_not_fine (Q : Nat) :
    ¬ IsTribonacciGap (Q + 1)
      (t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int))) := by
  intro hgap
  have hp : 0 < t ^ (-((Q + 1 : Nat) : Int)) := zpow_pos tribonacciConstant_pos _
  have hq : 0 < t ^ (-((Q + 2 : Nat) : Int)) := zpow_pos tribonacciConstant_pos _
  have hpr :
      t ^ (-((Q + 3 : Nat) : Int)) < t ^ (-((Q + 1 : Nat) : Int)) :=
    zpow_lt_zpow_right₀ one_lt_tribonacciConstant (by push_cast; omega)
  rcases hgap with hlarge | hsmall | hcombined
  · linarith
  · linarith
  · linarith

theorem large_gap_insertion_count (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1))
    (hlarge :
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
        t ^ (-(Q : Int))) :
    (insertedNameIndices Q i).card = 1 := by
  have hne : insertedNameIndices Q i ≠ ∅ := by
    intro hempty
    apply large_gap_not_fine Q
    rw [← hlarge]
    exact coarse_gap_is_fine_of_no_insertion Q i hempty
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hle := insertedNameIndices_card_le_one Q i
  have hpos : 0 < (insertedNameIndices Q i).card := Finset.card_pos.mpr ⟨j, hj⟩
  omega

theorem combined_gap_insertion_count (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1))
    (hcombined :
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
        t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int))) :
    (insertedNameIndices Q i).card = 1 := by
  have hne : insertedNameIndices Q i ≠ ∅ := by
    intro hempty
    apply combined_gap_not_fine Q
    rw [← hcombined]
    exact coarse_gap_is_fine_of_no_insertion Q i hempty
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hle := insertedNameIndices_card_le_one Q i
  have hpos : 0 < (insertedNameIndices Q i).card := Finset.card_pos.mpr ⟨j, hj⟩
  omega

/-- Small gaps insert no name; large and combined gaps insert exactly one. -/
theorem tribonacci_gap_insertion_count (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1)) :
    ((insertedNameIndices Q i).card = 0 ↔
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
        t ^ (-((Q + 1 : Nat) : Int))) ∧
    ((insertedNameIndices Q i).card = 1 ↔
      indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
          t ^ (-(Q : Int)) ∨
        indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
          t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int))) := by
  rcases consecutive_nameValue_gap Q i with hlarge | hsmall | hcombined
  · change indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
      t ^ (-(Q : Int)) at hlarge
    have hcard := large_gap_insertion_count Q i hlarge
    have hne : t ^ (-(Q : Int)) ≠ t ^ (-((Q + 1 : Nat) : Int)) := by
      exact ne_of_gt (zpow_lt_zpow_right₀ one_lt_tribonacciConstant (by push_cast; omega))
    constructor
    · constructor
      · intro hzero
        omega
      · intro hsmall
        exact (hne (hlarge.symm.trans hsmall)).elim
    · exact ⟨fun _ => Or.inl hlarge, fun _ => hcard⟩
  · change indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
      t ^ (-((Q + 1 : Nat) : Int)) at hsmall
    have hempty := small_gap_no_insertion Q i hsmall
    have hcard : (insertedNameIndices Q i).card = 0 := by rw [hempty]; rfl
    constructor
    · exact ⟨fun _ => hsmall, fun _ => hcard⟩
    · constructor
      · intro hone
        omega
      · intro hother
        rcases hother with hlarge | hcombined
        · have hne : t ^ (-(Q : Int)) ≠ t ^ (-((Q + 1 : Nat) : Int)) :=
            ne_of_gt (zpow_lt_zpow_right₀ one_lt_tribonacciConstant
              (by push_cast; omega))
          exact (hne (hlarge.symm.trans hsmall)).elim
        · have hpos : 0 < t ^ (-((Q + 2 : Nat) : Int)) :=
            zpow_pos tribonacciConstant_pos _
          linarith
  · change indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
      t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int)) at hcombined
    have hcard := combined_gap_insertion_count Q i hcombined
    have hne :
        t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int)) ≠
          t ^ (-((Q + 1 : Nat) : Int)) := by
      nlinarith [zpow_pos tribonacciConstant_pos (-((Q + 2 : Nat) : Int))]
    constructor
    · constructor
      · intro hzero
        omega
      · intro hsmall
        exact (hne (hcombined.symm.trans hsmall)).elim
    · exact ⟨fun _ => Or.inr hcombined, fun _ => hcard⟩

/-- The complete three-letter replacement law for one refinement step.

At level `Q+1`, a coarse small gap is one new large gap; a coarse large gap
is a new large gap followed by a new combined gap; and a coarse combined gap
is a new large gap followed by a new small gap. -/
theorem tribonacci_gap_substitution (Q : Nat)
    (i : Fin (tribonacci (Q + 2) - 1)) :
    (indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
          t ^ (-((Q + 1 : Nat) : Int)) →
        insertedNameIndices Q i = ∅ ∧
          indexedNameValue (Q + 1) (levelEmbedding Q (gapRight Q i)) -
              indexedNameValue (Q + 1) (levelEmbedding Q (gapLeft Q i)) =
            t ^ (-((Q + 1 : Nat) : Int))) ∧
    (indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
          t ^ (-(Q : Int)) →
        ∃ j : Fin (tribonacci (Q + 3)),
          insertedNameIndices Q i = {j} ∧
          indexedNameValue (Q + 1) j - indexedNameValue Q (gapLeft Q i) =
            t ^ (-((Q + 1 : Nat) : Int)) ∧
          indexedNameValue Q (gapRight Q i) - indexedNameValue (Q + 1) j =
            t ^ (-((Q + 2 : Nat) : Int)) + t ^ (-((Q + 3 : Nat) : Int))) ∧
    (indexedNameValue Q (gapRight Q i) - indexedNameValue Q (gapLeft Q i) =
          t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int)) →
        ∃ j : Fin (tribonacci (Q + 3)),
          insertedNameIndices Q i = {j} ∧
          indexedNameValue (Q + 1) j - indexedNameValue Q (gapLeft Q i) =
            t ^ (-((Q + 1 : Nat) : Int)) ∧
          indexedNameValue Q (gapRight Q i) - indexedNameValue (Q + 1) j =
            t ^ (-((Q + 2 : Nat) : Int))) := by
  constructor
  · intro hsmall
    constructor
    · exact small_gap_no_insertion Q i hsmall
    · rw [levelEmbedding_value, levelEmbedding_value]
      exact hsmall
  · constructor
    · intro hlarge
      obtain ⟨j, hjset⟩ := (Finset.card_eq_one.mp
        (large_gap_insertion_count Q i hlarge))
      have hj : j ∈ insertedNameIndices Q i := by rw [hjset]; simp
      have hvalue := insertedNameValue_eq Q i j hj
      have hrec := tribonacci_zpow_recurrence Q
      refine ⟨j, hjset, ?_, ?_⟩
      · linarith
      · linarith
    · intro hcombined
      obtain ⟨j, hjset⟩ := (Finset.card_eq_one.mp
        (combined_gap_insertion_count Q i hcombined))
      have hj : j ∈ insertedNameIndices Q i := by rw [hjset]; simp
      have hvalue := insertedNameValue_eq Q i j hj
      refine ⟨j, hjset, ?_, ?_⟩ <;> linarith

/-- The three letters in the Tribonacci adjacent-gap alphabet. -/
inductive TribonacciGapLetter
  | large
  | small
  | combined
  deriving DecidableEq

/-- The real length represented by a gap letter at level `Q`. -/
noncomputable def gapLetterLength (Q : Nat) : TribonacciGapLetter -> Real
  | .large => t ^ (-(Q : Int))
  | .small => t ^ (-((Q + 1 : Nat) : Int))
  | .combined =>
      t ^ (-((Q + 1 : Nat) : Int)) + t ^ (-((Q + 2 : Nat) : Int))

/-- The three-letter substitution read directly from `tribonacci_gap_substitution`. -/
def gapLetterSubstitution : TribonacciGapLetter -> List TribonacciGapLetter
  | .large => [.large, .combined]
  | .small => [.large]
  | .combined => [.large, .small]

def levelThreeGapWord : List TribonacciGapLetter :=
  [.large, .combined, .large, .small, .large, .combined]

def levelFourGapWord : List TribonacciGapLetter :=
  [.large, .combined, .large, .small, .large, .combined,
    .large, .large, .combined, .large, .small, .large]

example : adjacentNameValueGaps 3 = levelThreeGapWord.map (gapLetterLength 3) := by
  change [indexedNameValue 3 ⟨1, by decide⟩ - indexedNameValue 3 ⟨0, by decide⟩,
    indexedNameValue 3 ⟨2, by decide⟩ - indexedNameValue 3 ⟨1, by decide⟩,
    indexedNameValue 3 ⟨3, by decide⟩ - indexedNameValue 3 ⟨2, by decide⟩,
    indexedNameValue 3 ⟨4, by decide⟩ - indexedNameValue 3 ⟨3, by decide⟩,
    indexedNameValue 3 ⟨5, by decide⟩ - indexedNameValue 3 ⟨4, by decide⟩,
    indexedNameValue 3 ⟨6, by decide⟩ - indexedNameValue 3 ⟨5, by decide⟩] =
      [t ^ (-3 : Int), t ^ (-4 : Int) + t ^ (-5 : Int), t ^ (-3 : Int),
        t ^ (-4 : Int), t ^ (-3 : Int), t ^ (-4 : Int) + t ^ (-5 : Int)]
  rw [indexedNameValue_level_three_zero, indexedNameValue_level_three_one,
    indexedNameValue_level_three_two, indexedNameValue_level_three_three,
    indexedNameValue_level_three_four, indexedNameValue_level_three_five,
    indexedNameValue_level_three_six]
  simp only [List.cons.injEq, sub_zero, add_sub_cancel_left, true_and, and_true]
  have hrecOne : t ^ (-1 : Int) =
      t ^ (-2 : Int) + t ^ (-3 : Int) + t ^ (-4 : Int) := by
    convert tribonacci_zpow_recurrence 1 using 1 <;> norm_num
  have hrecTwo : t ^ (-2 : Int) =
      t ^ (-3 : Int) + t ^ (-4 : Int) + t ^ (-5 : Int) := by
    convert tribonacci_zpow_recurrence 2 using 1 <;> norm_num
  constructor
  · linarith
  · constructor <;> linarith

example : levelThreeGapWord.map gapLetterSubstitution =
    [[.large, .combined], [.large, .small], [.large, .combined], [.large],
      [.large, .combined], [.large, .small]] := by decide

example : adjacentNameValueGaps 4 = levelFourGapWord.map (gapLetterLength 4) := by
  change [indexedNameValue 4 ⟨1, by decide⟩ - indexedNameValue 4 ⟨0, by decide⟩,
    indexedNameValue 4 ⟨2, by decide⟩ - indexedNameValue 4 ⟨1, by decide⟩,
    indexedNameValue 4 ⟨3, by decide⟩ - indexedNameValue 4 ⟨2, by decide⟩,
    indexedNameValue 4 ⟨4, by decide⟩ - indexedNameValue 4 ⟨3, by decide⟩,
    indexedNameValue 4 ⟨5, by decide⟩ - indexedNameValue 4 ⟨4, by decide⟩,
    indexedNameValue 4 ⟨6, by decide⟩ - indexedNameValue 4 ⟨5, by decide⟩,
    indexedNameValue 4 ⟨7, by decide⟩ - indexedNameValue 4 ⟨6, by decide⟩,
    indexedNameValue 4 ⟨8, by decide⟩ - indexedNameValue 4 ⟨7, by decide⟩,
    indexedNameValue 4 ⟨9, by decide⟩ - indexedNameValue 4 ⟨8, by decide⟩,
    indexedNameValue 4 ⟨10, by decide⟩ - indexedNameValue 4 ⟨9, by decide⟩,
    indexedNameValue 4 ⟨11, by decide⟩ - indexedNameValue 4 ⟨10, by decide⟩,
    indexedNameValue 4 ⟨12, by decide⟩ - indexedNameValue 4 ⟨11, by decide⟩] =
      [t ^ (-4 : Int), t ^ (-5 : Int) + t ^ (-6 : Int), t ^ (-4 : Int),
        t ^ (-5 : Int), t ^ (-4 : Int), t ^ (-5 : Int) + t ^ (-6 : Int),
        t ^ (-4 : Int), t ^ (-4 : Int), t ^ (-5 : Int) + t ^ (-6 : Int),
        t ^ (-4 : Int), t ^ (-5 : Int), t ^ (-4 : Int)]
  rw [indexedNameValue_level_four_zero, indexedNameValue_level_four_one,
    indexedNameValue_level_four_two, indexedNameValue_level_four_three,
    indexedNameValue_level_four_four, indexedNameValue_level_four_five,
    indexedNameValue_level_four_six, indexedNameValue_level_four_seven,
    indexedNameValue_level_four_eight, indexedNameValue_level_four_nine,
    indexedNameValue_level_four_ten, indexedNameValue_level_four_eleven,
    indexedNameValue_level_four_twelve]
  simp only [List.cons.injEq, sub_zero, true_and, and_true]
  have hrecOne : t ^ (-1 : Int) =
      t ^ (-2 : Int) + t ^ (-3 : Int) + t ^ (-4 : Int) := by
    convert tribonacci_zpow_recurrence 1 using 1 <;> norm_num
  have hrecTwo : t ^ (-2 : Int) =
      t ^ (-3 : Int) + t ^ (-4 : Int) + t ^ (-5 : Int) := by
    convert tribonacci_zpow_recurrence 2 using 1 <;> norm_num
  have hrecThree : t ^ (-3 : Int) =
      t ^ (-4 : Int) + t ^ (-5 : Int) + t ^ (-6 : Int) := by
    convert tribonacci_zpow_recurrence 3 using 1 <;> norm_num
  constructor
  · linarith
  · constructor
    · linarith
    · constructor
      · linarith
      · constructor
        · linarith
        · constructor
          · linarith
          · constructor
            · linarith
            · constructor
              · linarith
              · constructor
                · linarith
                · constructor
                  · linarith
                  · constructor <;> linarith

example : levelFourGapWord.map gapLetterSubstitution =
    [[.large, .combined], [.large, .small], [.large, .combined], [.large],
      [.large, .combined], [.large, .small], [.large, .combined],
      [.large, .combined], [.large, .small], [.large, .combined], [.large],
      [.large, .combined]] := by decide

/-- Number of fine segments inside each coarse adjacent interval, in order. -/
def refinementBlockSizes (Q : Nat) : List Nat :=
  List.ofFn fun i : Fin (tribonacci (Q + 2) - 1) =>
    (levelEmbedding Q (gapRight Q i)).1 - (levelEmbedding Q (gapLeft Q i)).1

/-- Embedded endpoint positions for every coarse adjacent interval. -/
def refinementIndexTable (Q : Nat) : List (Nat × Nat) :=
  List.ofFn fun i : Fin (tribonacci (Q + 2) - 1) =>
    ((levelEmbedding Q (gapLeft Q i)).1, (levelEmbedding Q (gapRight Q i)).1)

example :
    (List.ofFn fun i : Fin 7 => (levelEmbedding 3 i).1) =
      [0, 2, 4, 6, 7, 9, 11] := by decide

example : refinementBlockSizes 3 = [2, 2, 2, 1, 2, 2] := by decide

example : refinementIndexTable 3 =
    [(0, 2), (2, 4), (4, 6), (6, 7), (7, 9), (9, 11)] := by decide

example :
    (List.ofFn fun i : Fin 13 => (levelEmbedding 4 i).1) =
      [0, 2, 4, 6, 7, 9, 11, 13, 15, 17, 19, 20, 22] := by decide

example : refinementBlockSizes 4 = [2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2] := by decide

example : refinementIndexTable 4 =
    [(0, 2), (2, 4), (4, 6), (6, 7), (7, 9), (9, 11),
      (11, 13), (13, 15), (15, 17), (17, 19), (19, 20), (20, 22)] := by decide

end D5.S0.Tower.Tribonacci.Substitution

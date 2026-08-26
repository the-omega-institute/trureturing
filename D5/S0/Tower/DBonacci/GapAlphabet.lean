/- GID: D5/S0/Tower/DBonacci/GapAlphabet
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacci/GapAlphabet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite d-bonacci gap letters realize the local refinement substitution. -/

import D5.S0.Tower.DBonacci.Substitution

namespace D5.S0.Tower.DBonacci.GapAlphabet

/-- The `d` letters carried by d-bonacci gaps. -/
def DBonacciGapLetter (d : Nat) := Fin d

instance (d : Nat) : Fintype (DBonacciGapLetter d) :=
  inferInstanceAs (Fintype (Fin d))

/-- The largest gap label. -/
def topGapLetter (d : Nat) (hd : 0 < d) : DBonacciGapLetter d :=
  ⟨d - 1, by omega⟩

/-- The real length represented by a d-bonacci gap letter at level `Q`. -/
noncomputable def gapLetterLength (d Q : Nat) (letter : DBonacciGapLetter d) : Real :=
  D5.S0.Tower.DBonacci.Gaps.dbonacciGapLength d Q letter.1

/-- Zero becomes the top letter; a successor becomes top followed by predecessor. -/
def gapLetterSubstitution (d : Nat) (hd : 0 < d) (letter : DBonacciGapLetter d) :
    List (DBonacciGapLetter d) :=
  if hzero : letter.1 = 0 then
    [topGapLetter d hd]
  else
    [topGapLetter d hd, ⟨letter.1 - 1, by omega⟩]

/-- A fine interval realizes a one- or two-letter refinement word. -/
def RealizesGapRefinement (d Q : Nat)
    (i : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d (Q + 2) - 1)) :
    List (DBonacciGapLetter d) -> Prop
  | [fine] =>
      D5.S0.Tower.DBonacci.Substitution.insertedNameIndices d Q i = ∅ ∧
        D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1)
              (D5.S0.Tower.DBonacci.Substitution.levelEmbedding d Q
                (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i)) -
            D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1)
              (D5.S0.Tower.DBonacci.Substitution.levelEmbedding d Q
                (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i)) =
          gapLetterLength d (Q + 1) fine
  | [left, right] =>
      ∃ j : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d (Q + 3)),
        D5.S0.Tower.DBonacci.Substitution.insertedNameIndices d Q i = {j} ∧
          D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1) j -
              D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
                (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i) =
            gapLetterLength d (Q + 1) left ∧
          D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
                (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i) -
              D5.S0.Tower.DBonacci.Values.indexedNameValue d (Q + 1) j =
            gapLetterLength d (Q + 1) right
  | _ => False

/-- Letter lengths satisfy the same replacement law as the letters. -/
theorem gapLetterLength_substitution (d Q : Nat) (hd : 2 ≤ d)
    (letter : DBonacciGapLetter d) :
    gapLetterLength d Q letter =
      ((gapLetterSubstitution d (by omega) letter).map
        (gapLetterLength d (Q + 1))).sum := by
  by_cases hzero : letter.1 = 0
  · have h := D5.S0.Tower.DBonacci.Substitution.gapLength_zero_substitution d Q hd
    simpa [gapLetterLength, gapLetterSubstitution, hzero, topGapLetter,
      List.map, List.sum_cons, List.sum_nil] using h
  · obtain ⟨fuel, hfuel⟩ : ∃ fuel, letter.1 = fuel + 1 := by
      exact ⟨letter.1 - 1, by omega⟩
    have h := D5.S0.Tower.DBonacci.Substitution.gapLength_succ_substitution d Q fuel hd
    simpa [gapLetterLength, gapLetterSubstitution, hzero, topGapLetter, hfuel,
      List.map, List.sum_cons, List.sum_nil] using h

/-- Every coarse gap geometrically realizes its letter substitution inside the interval. -/
theorem dbonacci_gap_letter_substitution (d Q : Nat) (hd : 2 ≤ d)
    (i : Fin (D5.S0.Tower.DBonacci.Names.dbonacci d (Q + 2) - 1)) :
    ∃ letter : DBonacciGapLetter d,
      letter.1 ∈ Finset.Ico (d - Q) d ∧
        D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
              (D5.S0.Tower.DBonacci.Substitution.gapRight d Q i) -
            D5.S0.Tower.DBonacci.Values.indexedNameValue d Q
              (D5.S0.Tower.DBonacci.Substitution.gapLeft d Q i) =
          gapLetterLength d Q letter ∧
        RealizesGapRefinement d Q i
          (gapLetterSubstitution d (by omega) letter) := by
  obtain ⟨label, hlabel, hgap, hrefinement⟩ :=
    D5.S0.Tower.DBonacci.Substitution.dbonacci_gap_substitution d Q hd i
  have hlt : label < d := (Finset.mem_Ico.mp hlabel).2
  let letter : DBonacciGapLetter d := ⟨label, hlt⟩
  refine ⟨letter, hlabel, ?_, ?_⟩
  · exact hgap
  · cases label with
    | zero =>
        simpa [letter, gapLetterSubstitution, topGapLetter, gapLetterLength,
          RealizesGapRefinement] using hrefinement
    | succ fuel =>
        simpa [letter, gapLetterSubstitution, topGapLetter, gapLetterLength,
          RealizesGapRefinement] using hrefinement

/-- Identification of the order-three letters with the frozen Tribonacci alphabet. -/
def dbonacciGapLetterThreeEquiv : DBonacciGapLetter 3 ≃
    D5.S0.Tower.Tribonacci.Substitution.TribonacciGapLetter where
  toFun letter :=
    D5.S0.Tower.DBonacci.Substitution.tribonacciGapLetterOfLabel letter.1
  invFun
    | .small => ⟨0, by omega⟩
    | .combined => ⟨1, by omega⟩
    | .large => ⟨2, by omega⟩
  left_inv letter := by
    fin_cases letter <;> rfl
  right_inv letter := by
    cases letter <;>
      norm_num [D5.S0.Tower.DBonacci.Substitution.tribonacciGapLetterOfLabel]

/-- The typed order-three substitution is exactly the frozen Tribonacci substitution. -/
theorem dbonacciGapLetterSubstitution_three_eq_tribonacciGapLetterSubstitution :
    (fun letter : DBonacciGapLetter 3 =>
      (gapLetterSubstitution 3 (by omega) letter).map dbonacciGapLetterThreeEquiv) =
    (fun letter : DBonacciGapLetter 3 =>
      D5.S0.Tower.Tribonacci.Substitution.gapLetterSubstitution
        (dbonacciGapLetterThreeEquiv letter)) := by
  funext letter
  fin_cases letter <;>
    norm_num [gapLetterSubstitution, List.map, topGapLetter, dbonacciGapLetterThreeEquiv,
      D5.S0.Tower.DBonacci.Substitution.tribonacciGapLetterOfLabel,
      D5.S0.Tower.Tribonacci.Substitution.gapLetterSubstitution]

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- Order-three letter lengths are exactly the frozen Tribonacci letter lengths. -/
theorem dbonacciGapLetterLength_three_eq_tribonacciGapLetterLength (Q : Nat) :
    gapLetterLength 3 Q =
      fun letter : DBonacciGapLetter 3 =>
        D5.S0.Tower.Tribonacci.Substitution.gapLetterLength Q
          (dbonacciGapLetterThreeEquiv letter) := by
  funext letter
  have hQ :
      (D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^ Q)⁻¹ =
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^ (-(Q : Int)) := by
    rw [zpow_neg]
    norm_num
  have hOne : D5.S0.Tower.Tribonacci.Values.tribonacciConstant⁻¹ =
      D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^ (-1 : Int) := by
    norm_num [zpow_neg]
  have hTwo :
      (∑ x ∈ Finset.range 2,
          (D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^ (x + 1))⁻¹) =
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^ (-1 : Int) +
          D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^ (-2 : Int) := by
    norm_num [Finset.sum_range_succ, zpow_neg]
    all_goals rfl
  have hThree :
      (∑ x ∈ Finset.range 3,
          (D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^ (x + 1))⁻¹) =
        D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^ (-1 : Int) +
          D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^ (-2 : Int) +
            D5.S0.Tower.Tribonacci.Values.tribonacciConstant ^ (-3 : Int) := by
    norm_num [Finset.sum_range_succ, zpow_neg]
    all_goals rfl
  fin_cases letter
  · norm_num [gapLetterLength, D5.S0.Tower.DBonacci.Gaps.dbonacciGapLength,
      D5.S0.Tower.DBonacci.Gaps.dbonacciBudgetBound,
      D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant,
      dbonacciGapLetterThreeEquiv,
      D5.S0.Tower.DBonacci.Substitution.tribonacciGapLetterOfLabel,
      D5.S0.Tower.Tribonacci.Substitution.gapLetterLength]
    rw [hQ, hOne, D5.S0.Tower.Tribonacci.Values.tribonacci_zpow_mul]
    congr 1
    omega
  · norm_num [gapLetterLength, D5.S0.Tower.DBonacci.Gaps.dbonacciGapLength,
      D5.S0.Tower.DBonacci.Gaps.dbonacciBudgetBound,
      D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant,
      dbonacciGapLetterThreeEquiv,
      D5.S0.Tower.DBonacci.Substitution.tribonacciGapLetterOfLabel,
      D5.S0.Tower.Tribonacci.Substitution.gapLetterLength]
    rw [hQ, hTwo, mul_add, D5.S0.Tower.Tribonacci.Values.tribonacci_zpow_mul,
      D5.S0.Tower.Tribonacci.Values.tribonacci_zpow_mul]
    congr 1 <;> ring_nf
  · norm_num [gapLetterLength, D5.S0.Tower.DBonacci.Gaps.dbonacciGapLength,
      D5.S0.Tower.DBonacci.Gaps.dbonacciBudgetBound,
      D5.S0.Tower.DBonacci.PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant,
      dbonacciGapLetterThreeEquiv,
      D5.S0.Tower.DBonacci.Substitution.tribonacciGapLetterOfLabel,
      D5.S0.Tower.Tribonacci.Substitution.gapLetterLength]
    rw [hQ, hThree, D5.S0.Tower.Tribonacci.Values.tribonacci_inverse_sum]
    ring

/-- The order-three geometric witness transports to the frozen replacement word. -/
theorem dbonacci_gap_letter_substitution_three_consistent_with_tribonacci
    (Q : Nat)
    (i : Fin (D5.S0.Tower.DBonacci.Names.dbonacci 3 (Q + 2) - 1)) :
    ∃ letter : DBonacciGapLetter 3,
      letter.1 ∈ Finset.Ico (3 - Q) 3 ∧
        D5.S0.Tower.DBonacci.Values.indexedNameValue 3 Q
              (D5.S0.Tower.DBonacci.Substitution.gapRight 3 Q i) -
            D5.S0.Tower.DBonacci.Values.indexedNameValue 3 Q
              (D5.S0.Tower.DBonacci.Substitution.gapLeft 3 Q i) =
          gapLetterLength 3 Q letter ∧
        RealizesGapRefinement 3 Q i
          (gapLetterSubstitution 3 (by omega) letter) ∧
        (gapLetterSubstitution 3 (by omega) letter).map
            dbonacciGapLetterThreeEquiv =
          D5.S0.Tower.Tribonacci.Substitution.gapLetterSubstitution
            (dbonacciGapLetterThreeEquiv letter) := by
  obtain ⟨letter, hallowed, hlength, hrefinement⟩ :=
    dbonacci_gap_letter_substitution 3 Q (by omega) i
  refine ⟨letter, hallowed, hlength, hrefinement, ?_⟩
  exact congrFun
    dbonacciGapLetterSubstitution_three_eq_tribonacciGapLetterSubstitution letter

end D5.S0.Tower.DBonacci.GapAlphabet

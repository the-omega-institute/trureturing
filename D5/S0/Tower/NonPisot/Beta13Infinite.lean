/- GID: D5/S0/Tower/NonPisot/Beta13Infinite
   generality: G
   mirror-B: D5/B/S0/Tower/NonPisot/Beta13Infinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact infinite greedy digit and remainder streams for the quadratic base beta13. -/

import D5.S0.Tower.NonPisot.Beta13
import Mathlib.Tactic

namespace D5.S0.Tower.NonPisot.Beta13Infinite

/- Library search receipt (2026-08-18):
   * Repository and pinned-mathlib searches found no beta-expansion or Parry-language API.
   * Loogle found the generic `Int.floor_*` and `Int.fract_*` lemmas used below.
   * LeanSearch returned no result for `greedy beta expansion Parry admissible`.
   The exact quadratic comparison and stream are therefore implemented locally. -/

/-- An exact code `(a,b)` represents `a + b * beta13`. -/
abbrev Beta13Code := Int × Int

/-- Real interpretation of an exact quadratic code. -/
noncomputable def beta13CodeValue (code : Beta13Code) : Real :=
  (code.1 : Real) + (code.2 : Real) *
    D5.S0.Tower.NonPisot.Beta13.beta13

/-- Multiplication by beta13, reduced using `beta13^2 = beta13 + 3`. -/
def beta13CodeMul (code : Beta13Code) : Beta13Code :=
  (3 * code.2, code.1 + code.2)

/-- Subtraction of an integer digit from a quadratic code. -/
def beta13CodeSubDigit (code : Beta13Code) (digit : Int) : Beta13Code :=
  (code.1 - digit, code.2)

/-- Addition of an integer digit to a normalized name code. -/
def beta13CodeAddDigit (code : Beta13Code) (digit : Int) : Beta13Code :=
  (code.1 + digit, code.2)

/-- Difference of two exact quadratic codes. -/
def beta13CodeSub (left right : Beta13Code) : Beta13Code :=
  (left.1 - right.1, left.2 - right.2)

/-- Multiplication of codes agrees with multiplication by the real base. -/
theorem beta13_code_value_mul (code : Beta13Code) :
    beta13CodeValue (beta13CodeMul code) =
      D5.S0.Tower.NonPisot.Beta13.beta13 * beta13CodeValue code := by
  rw [beta13CodeValue, beta13CodeValue, beta13CodeMul]
  push_cast
  ring_nf
  rw [D5.S0.Tower.NonPisot.Beta13.beta13_sq]
  ring

/-- Subtracting a digit from a code subtracts the corresponding real integer. -/
theorem beta13_code_value_sub_digit (code : Beta13Code) (digit : Int) :
    beta13CodeValue (beta13CodeSubDigit code digit) =
      beta13CodeValue code - digit := by
  rw [beta13CodeValue, beta13CodeValue, beta13CodeSubDigit]
  push_cast
  ring

/-- Distinct integral codes have distinct real values. -/
theorem beta13_code_value_injective : Function.Injective beta13CodeValue := by
  intro left right hvalue
  by_cases hsecond : left.2 = right.2
  · have hfirstReal : (left.1 : Real) = (right.1 : Real) := by
      rw [beta13CodeValue, beta13CodeValue, hsecond] at hvalue
      linarith
    have hfirst : left.1 = right.1 := by exact_mod_cast hfirstReal
    exact Prod.ext hfirst hsecond
  · exfalso
    apply D5.S0.Tower.NonPisot.Beta13.beta13_irrational.ne_rational
      (right.1 - left.1) (left.2 - right.2)
    field_simp [sub_ne_zero.mpr hsecond]
    rw [beta13CodeValue, beta13CodeValue] at hvalue
    push_cast at hvalue ⊢
    nlinarith

/-- Executable sign test for the quadratic expression `m + b * sqrt 13`. -/
def beta13SqrtLinearNegative (m b : Int) : Bool :=
  decide (
    (0 < b ∧ m < 0 ∧ 13 * b ^ 2 < m ^ 2) ∨
    (b < 0 ∧ (m ≤ 0 ∨ m ^ 2 < 13 * b ^ 2)) ∨
    (b = 0 ∧ m < 0))

/-- The integer sign test exactly decides negativity of `m + b * sqrt 13`. -/
theorem beta13_sqrt_linear_negative_iff (m b : Int) :
    beta13SqrtLinearNegative m b = true ↔
      (m : Real) + (b : Real) * Real.sqrt 13 < 0 := by
  have hsqrtSq : Real.sqrt (13 : Real) ^ 2 = 13 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt (13 : Real) := Real.sqrt_nonneg 13
  have hsqrtPos : 0 < Real.sqrt (13 : Real) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtScaledSq (z : Real) :
      (z * Real.sqrt 13) ^ 2 = 13 * z ^ 2 := by
    rw [mul_pow, hsqrtSq]
    ring
  simp only [beta13SqrtLinearNegative, decide_eq_true_eq]
  constructor
  · rintro (hpos | hneg | hzero)
    · rcases hpos with ⟨hb, hm, hsq⟩
      have hbR : (0 : Real) < b := by exact_mod_cast hb
      have hmR : (m : Real) < 0 := by exact_mod_cast hm
      have hsqR : (13 : Real) * (b : Real) ^ 2 < (m : Real) ^ 2 := by
        exact_mod_cast hsq
      have hleft : 0 ≤ (b : Real) * Real.sqrt 13 :=
        mul_nonneg hbR.le hsqrtNonneg
      have hright : 0 ≤ -(m : Real) := by linarith
      have hsquares :
          ((b : Real) * Real.sqrt 13) ^ 2 < (-(m : Real)) ^ 2 := by
        rw [hsqrtScaledSq]
        nlinarith
      have hlt := (sq_lt_sq₀ hleft hright).mp hsquares
      nlinarith
    · rcases hneg with ⟨hb, hm | hsq⟩
      · have hbR : (b : Real) < 0 := by exact_mod_cast hb
        have hmR : (m : Real) ≤ 0 := by exact_mod_cast hm
        nlinarith
      · have hbR : (b : Real) < 0 := by exact_mod_cast hb
        have hsqR : (m : Real) ^ 2 < (13 : Real) * (b : Real) ^ 2 := by
          exact_mod_cast hsq
        rcases le_or_gt m 0 with hm | hm
        · have hmR : (m : Real) ≤ 0 := by exact_mod_cast hm
          nlinarith
        · have hmR : (0 : Real) < m := by exact_mod_cast hm
          have hright : 0 ≤ (-(b : Real)) * Real.sqrt 13 :=
            mul_nonneg (by linarith) hsqrtNonneg
          have hsquares :
              (m : Real) ^ 2 < ((-(b : Real)) * Real.sqrt 13) ^ 2 := by
            rw [hsqrtScaledSq]
            nlinarith
          have hlt := (sq_lt_sq₀ hmR.le hright).mp hsquares
          nlinarith
    · rcases hzero with ⟨hb, hm⟩
      have hbR : (b : Real) = 0 := by exact_mod_cast hb
      have hmR : (m : Real) < 0 := by exact_mod_cast hm
      nlinarith
  · intro hvalue
    rcases lt_trichotomy b 0 with hb | hb | hb
    · apply Or.inr
      apply Or.inl
      refine ⟨hb, ?_⟩
      rcases le_or_gt m 0 with hm | hm
      · exact Or.inl hm
      · apply Or.inr
        have hbR : (b : Real) < 0 := by exact_mod_cast hb
        have hmR : (0 : Real) < m := by exact_mod_cast hm
        have hright : 0 ≤ (-(b : Real)) * Real.sqrt 13 :=
          mul_nonneg (by linarith) hsqrtNonneg
        have hlt : (m : Real) < (-(b : Real)) * Real.sqrt 13 := by
          nlinarith
        have hsqR : (m : Real) ^ 2 < (13 : Real) * (b : Real) ^ 2 := by
          have hsquares := (sq_lt_sq₀ hmR.le hright).mpr hlt
          rw [hsqrtScaledSq] at hsquares
          nlinarith
        exact_mod_cast hsqR
    · apply Or.inr
      apply Or.inr
      refine ⟨hb, ?_⟩
      have hbR : (b : Real) = 0 := by exact_mod_cast hb
      by_contra hm
      have hmInt : (0 : Int) ≤ m := Int.le_of_not_gt hm
      have hmR : (0 : Real) ≤ m := by exact_mod_cast hmInt
      nlinarith
    · apply Or.inl
      have hm : m < 0 := by
        by_contra hm
        have hbR : (0 : Real) < b := by exact_mod_cast hb
        have hmInt : (0 : Int) ≤ m := Int.le_of_not_gt hm
        have hmR : (0 : Real) ≤ m := by exact_mod_cast hmInt
        nlinarith
      refine ⟨hb, hm, ?_⟩
      have hbR : (0 : Real) < b := by exact_mod_cast hb
      have hmR : (m : Real) < 0 := by exact_mod_cast hm
      have hleft : 0 ≤ (b : Real) * Real.sqrt 13 :=
        mul_nonneg hbR.le hsqrtNonneg
      have hright : 0 ≤ -(m : Real) := by linarith
      have hlt : (b : Real) * Real.sqrt 13 < -(m : Real) := by
        nlinarith
      have hsqR : (13 : Real) * (b : Real) ^ 2 < (m : Real) ^ 2 := by
        have hsquares := (sq_lt_sq₀ hleft hright).mpr hlt
        rw [hsqrtScaledSq] at hsquares
        nlinarith
      exact_mod_cast hsqR

/-- Executable exact comparison of a quadratic code with an integer. -/
def beta13CodeLtInt (code : Beta13Code) (bound : Int) : Bool :=
  beta13SqrtLinearNegative
    (2 * code.1 + code.2 - 2 * bound) code.2

/-- The executable comparison agrees with the real ordering. -/
theorem beta13_code_lt_int_iff (code : Beta13Code) (bound : Int) :
    beta13CodeLtInt code bound = true ↔ beta13CodeValue code < bound := by
  rw [beta13CodeLtInt, beta13_sqrt_linear_negative_iff]
  rw [beta13CodeValue, D5.S0.Tower.NonPisot.Beta13.beta13]
  push_cast
  constructor <;> intro h <;> nlinarith

/-- The greedy digit selected from an exact remainder code. -/
def beta13CodeDigit (code : Beta13Code) : Int :=
  if beta13CodeLtInt (beta13CodeMul code) 1 then 0
  else if beta13CodeLtInt (beta13CodeMul code) 2 then 1
  else 2

/-- On the invariant remainder interval, the executable digit is the real floor digit. -/
theorem beta13_code_digit_eq_floor (code : Beta13Code)
    (hcode : 0 ≤ beta13CodeValue code ∧ beta13CodeValue code ≤ 1) :
    beta13CodeDigit code =
      ⌊D5.S0.Tower.NonPisot.Beta13.beta13 * beta13CodeValue code⌋ := by
  have hbeta := D5.S0.Tower.NonPisot.Beta13.beta13_between_two_three
  have hnonneg :
      0 ≤ D5.S0.Tower.NonPisot.Beta13.beta13 * beta13CodeValue code :=
    mul_nonneg (le_trans (by norm_num) hbeta.1.le) hcode.1
  have hupper :
      D5.S0.Tower.NonPisot.Beta13.beta13 * beta13CodeValue code < 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hcode.2
      (le_trans (by norm_num) hbeta.1.le)]
  rw [beta13CodeDigit]
  split <;> rename_i hone
  · rw [beta13_code_lt_int_iff, beta13_code_value_mul] at hone
    apply Eq.symm
    apply Int.floor_eq_iff.mpr
    constructor
    · norm_num
      exact hnonneg
    · norm_num
      norm_num at hone
      exact hone
  · have hone' :
        (1 : Real) ≤
          D5.S0.Tower.NonPisot.Beta13.beta13 * beta13CodeValue code := by
      have hnot : ¬beta13CodeValue (beta13CodeMul code) < ((1 : Int) : Real) :=
        fun h => hone ((beta13_code_lt_int_iff _ _).mpr h)
      rw [beta13_code_value_mul] at hnot
      norm_num at hnot
      exact hnot
    split <;> rename_i htwo
    · rw [beta13_code_lt_int_iff, beta13_code_value_mul] at htwo
      apply Eq.symm
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num
        exact hone'
      · norm_num
        exact htwo
    · have htwo' :
          (2 : Real) ≤
            D5.S0.Tower.NonPisot.Beta13.beta13 * beta13CodeValue code := by
        have hnot : ¬beta13CodeValue (beta13CodeMul code) < ((2 : Int) : Real) :=
          fun h => htwo ((beta13_code_lt_int_iff _ _).mpr h)
        rw [beta13_code_value_mul] at hnot
        exact le_of_not_gt hnot
      apply Eq.symm
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num
        exact htwo'
      · norm_num
        exact hupper

/-- Exact infinite stream of greedy remainder codes, beginning with the code for one. -/
def beta13RemainderCode : Nat → Beta13Code
  | 0 => (1, 0)
  | n + 1 =>
      beta13CodeSubDigit (beta13CodeMul (beta13RemainderCode n))
        (beta13CodeDigit (beta13RemainderCode n))

/-- Exact infinite greedy digit stream. -/
def beta13GreedyDigit (n : Nat) : Int :=
  beta13CodeDigit (beta13RemainderCode n)

/-- Real-valued infinite remainder stream. -/
noncomputable def beta13RemainderValue (n : Nat) : Real :=
  beta13CodeValue (beta13RemainderCode n)

/-- Exact-code remainders obey the beta-transformation recurrence. -/
theorem beta13_remainder_value_succ (n : Nat) :
    beta13RemainderValue (n + 1) =
      D5.S0.Tower.NonPisot.Beta13.beta13 * beta13RemainderValue n -
        beta13GreedyDigit n := by
  rw [beta13RemainderValue, beta13RemainderValue, beta13RemainderCode,
    beta13GreedyDigit, beta13_code_value_sub_digit, beta13_code_value_mul]

/-- Every exact remainder lies in the closed unit interval. -/
theorem beta13_remainder_value_in_unit_interval (n : Nat) :
    0 ≤ beta13RemainderValue n ∧ beta13RemainderValue n ≤ 1 := by
  induction n with
  | zero =>
      norm_num [beta13RemainderValue, beta13RemainderCode, beta13CodeValue]
  | succ n ih =>
      have hdigit : beta13GreedyDigit n =
          ⌊D5.S0.Tower.NonPisot.Beta13.beta13 * beta13RemainderValue n⌋ := by
        rw [beta13GreedyDigit, beta13RemainderValue]
        exact beta13_code_digit_eq_floor (beta13RemainderCode n) ih
      rw [beta13_remainder_value_succ, hdigit]
      constructor
      · simpa only [Int.self_sub_floor] using Int.fract_nonneg
          (D5.S0.Tower.NonPisot.Beta13.beta13 * beta13RemainderValue n)
      · exact (by simpa only [Int.self_sub_floor] using
          (Int.fract_lt_one
            (D5.S0.Tower.NonPisot.Beta13.beta13 * beta13RemainderValue n)).le)

/-- The executable digit stream is the greedy real floor stream at every index. -/
theorem beta13_greedy_digit_eq_floor (n : Nat) :
    beta13GreedyDigit n =
      ⌊D5.S0.Tower.NonPisot.Beta13.beta13 * beta13RemainderValue n⌋ := by
  exact beta13_code_digit_eq_floor (beta13RemainderCode n)
    (beta13_remainder_value_in_unit_interval n)

/-- The remainder recurrence written solely with the real floor digit. -/
theorem beta13_remainder_floor_recurrence (n : Nat) :
    beta13RemainderValue (n + 1) =
      D5.S0.Tower.NonPisot.Beta13.beta13 * beta13RemainderValue n -
        ⌊D5.S0.Tower.NonPisot.Beta13.beta13 * beta13RemainderValue n⌋ := by
  rw [← beta13_greedy_digit_eq_floor, beta13_remainder_value_succ]

/-- One exact beta-transformation step on a remainder code. -/
def beta13NextRemainderCode (code : Beta13Code) : Beta13Code :=
  beta13CodeSubDigit (beta13CodeMul code) (beta13CodeDigit code)

/-- A finite view of the infinite stream, computed by threading the exact remainder state. -/
def beta13GreedyPrefixFrom : Beta13Code → Nat → List Int
  | _, 0 => []
  | code, Q + 1 =>
      beta13CodeDigit code ::
        beta13GreedyPrefixFrom (beta13NextRemainderCode code) Q

/-- Threading from remainder `n` produces the corresponding slice of the infinite stream. -/
theorem beta13_greedy_prefix_from_remainder (n Q : Nat) :
    beta13GreedyPrefixFrom (beta13RemainderCode n) Q =
      List.ofFn (fun i : Fin Q => beta13GreedyDigit (n + i)) := by
  induction Q generalizing n with
  | zero => rfl
  | succ Q ih =>
      rw [beta13GreedyPrefixFrom, List.ofFn_succ]
      congr 1
      rw [show beta13NextRemainderCode (beta13RemainderCode n) =
        beta13RemainderCode (n + 1) by rfl, ih]
      apply congrArg List.ofFn
      funext i
      apply congrArg beta13GreedyDigit
      simp only [Fin.val_succ]
      omega

/-- The length-`Q` prefix of the genuine infinite greedy digit stream. -/
def beta13GreedyPrefix (Q : Nat) : List Int :=
  beta13GreedyPrefixFrom (1, 0) Q

/-- The threaded prefix is extensionally the prefix selected from the infinite digit function. -/
theorem beta13_greedy_prefix_eq_ofFn (Q : Nat) :
    beta13GreedyPrefix Q = List.ofFn (fun i : Fin Q => beta13GreedyDigit i) := by
  rw [beta13GreedyPrefix, show (1, 0) = beta13RemainderCode 0 by rfl,
    beta13_greedy_prefix_from_remainder]
  apply congrArg List.ofFn
  funext i
  simp

/-- The digit alphabet for beta13, whose floor digits are zero, one, and two. -/
def beta13DigitAlphabet : List Int := [0, 1, 2]

/-- A word is no greater than the matching prefix of the infinite greedy stream. -/
def beta13BelowGreedyPrefix (word : List Int) : Bool :=
  compare word (beta13GreedyPrefix word.length) != .gt

/-- At every word length, the executable test uses the matching prefix of the infinite stream. -/
theorem beta13_below_greedy_prefix_iff_infinite_stream (word : List Int) :
    beta13BelowGreedyPrefix word = true ↔
      compare word
        (List.ofFn (fun i : Fin word.length => beta13GreedyDigit i)) != .gt := by
  rw [beta13BelowGreedyPrefix, beta13_greedy_prefix_eq_ofFn]

/-- All digits belong to the beta13 alphabet and every suffix passes the greedy-prefix test. -/
def Beta13Admissible (word : List Int) : Prop :=
  word.Forall (· ∈ beta13DigitAlphabet) ∧
    word.tails.Forall (beta13BelowGreedyPrefix · = true)

noncomputable instance beta13AdmissibleDecidable (word : List Int) :
    Decidable (Beta13Admissible word) :=
  Classical.propDecidable _

/-- Admissibility of a nonempty word separates into its head, full-word test, and tail. -/
theorem beta13_admissible_cons_iff (digit : Int) (tail : List Int) :
    Beta13Admissible (digit :: tail) ↔
      digit ∈ beta13DigitAlphabet ∧
        beta13BelowGreedyPrefix (digit :: tail) = true ∧
          Beta13Admissible tail := by
  simp only [Beta13Admissible, List.forall_cons, List.tails, and_assoc]
  tauto

/-- The empty word is admissible. -/
theorem beta13_admissible_nil : Beta13Admissible [] := by
  norm_num [Beta13Admissible, beta13BelowGreedyPrefix, beta13GreedyPrefix]
  decide

/-- One recursive step retaining exactly the newly formed admissible full words. -/
def beta13NameStep (tails : List (List Int)) : List (List Int) :=
  beta13DigitAlphabet.flatMap fun digit =>
    tails.filterMap fun tail =>
      let word := digit :: tail
      if beta13BelowGreedyPrefix word then some word else none

/-- Length-`Q` names obtained by iterating the admissible-word step. -/
def beta13Names : Nat → List (List Int)
  | 0 => [[]]
  | Q + 1 => beta13NameStep (beta13Names Q)

/-- Membership in one generator step records a digit, an old tail, and the new full-word test. -/
theorem mem_beta13_names_succ_iff (Q : Nat) (word : List Int) :
    word ∈ beta13Names (Q + 1) ↔
      ∃ digit ∈ beta13DigitAlphabet, ∃ tail ∈ beta13Names Q,
        beta13BelowGreedyPrefix (digit :: tail) = true ∧ digit :: tail = word := by
  simp only [beta13Names, beta13NameStep, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨digit, hdigit, tail, htail, hif⟩
    split at hif <;> rename_i htest
    · exact ⟨digit, hdigit, tail, htail, htest, Option.some.inj hif⟩
    · cases hif
  · rintro ⟨digit, hdigit, tail, htail, htest, rfl⟩
    refine ⟨digit, hdigit, tail, htail, ?_⟩
    simp [htest]

/-- For every level, the recursive generator implements the genuine infinite-prefix criterion. -/
theorem mem_beta13_names_iff_admissible (Q : Nat) (word : List Int) :
    word ∈ beta13Names Q ↔ word.length = Q ∧ Beta13Admissible word := by
  induction Q generalizing word with
  | zero =>
      constructor
      · intro hword
        simp only [beta13Names, List.mem_singleton] at hword
        subst word
        exact ⟨rfl, beta13_admissible_nil⟩
      · rintro ⟨hlength, _⟩
        cases word with
        | nil => simp [beta13Names]
        | cons head tail => simp at hlength
  | succ Q ih =>
      rw [mem_beta13_names_succ_iff]
      constructor
      · rintro ⟨digit, hdigit, tail, htail, htest, rfl⟩
        have htail' := (ih tail).mp htail
        refine ⟨by simp [htail'.1], ?_⟩
        rw [beta13_admissible_cons_iff]
        exact ⟨hdigit, htest, htail'.2⟩
      · rintro ⟨hlength, hadmissible⟩
        cases word with
        | nil => simp at hlength
        | cons digit tail =>
            have htailLength : tail.length = Q := by
              simpa only [List.length_cons, Nat.succ.injEq] using hlength
            have hparts := (beta13_admissible_cons_iff digit tail).mp hadmissible
            exact ⟨digit, hparts.1, tail,
              (ih tail).mpr ⟨htailLength, hparts.2.2⟩, hparts.2.1, rfl⟩

/-- The code for beta13^Q times the value of a length-`Q` name. -/
def beta13NormalizedNameCode (word : List Int) : Beta13Code :=
  word.foldl
    (fun code digit => beta13CodeAddDigit (beta13CodeMul code) digit) (0, 0)

/-- Differences between consecutive entries of an exact ordered code list. -/
def beta13AdjacentCodeDifferences : List Beta13Code → List Beta13Code
  | left :: right :: rest =>
      beta13CodeSub right left :: beta13AdjacentCodeDifferences (right :: rest)
  | _ => []

/-- Exact normalized internal adjacent-gap types in the infinite-prefix model. -/
def beta13NormalizedGapCodes (Q : Nat) : Finset Beta13Code :=
  (beta13AdjacentCodeDifferences
    ((beta13Names Q).map beta13NormalizedNameCode)).toFinset

/-- Real normalized internal adjacent-gap types in the infinite-prefix model. -/
noncomputable def beta13NormalizedGapSpectrum (Q : Nat) : Finset Real :=
  (beta13NormalizedGapCodes Q).image beta13CodeValue

/- This finite list is only a proof certificate for the Q=6 reproof. The model's digit stream
   remains the unbounded function `beta13GreedyDigit`. -/
def beta13NamesFiveCertificate : List (List Int) := [
  [0,0,0,0,0], [0,0,0,0,1], [0,0,0,0,2], [0,0,0,1,0], [0,0,0,1,1],
  [0,0,0,1,2], [0,0,0,2,0], [0,0,1,0,0], [0,0,1,0,1], [0,0,1,0,2],
  [0,0,1,1,0], [0,0,1,1,1], [0,0,1,1,2], [0,0,1,2,0], [0,0,2,0,0],
  [0,0,2,0,1], [0,1,0,0,0], [0,1,0,0,1], [0,1,0,0,2], [0,1,0,1,0],
  [0,1,0,1,1], [0,1,0,1,2], [0,1,0,2,0], [0,1,1,0,0], [0,1,1,0,1],
  [0,1,1,0,2], [0,1,1,1,0], [0,1,1,1,1], [0,1,1,1,2], [0,1,1,2,0],
  [0,1,2,0,0], [0,1,2,0,1], [0,2,0,0,0], [0,2,0,0,1], [0,2,0,0,2],
  [0,2,0,1,0], [0,2,0,1,1], [1,0,0,0,0], [1,0,0,0,1], [1,0,0,0,2],
  [1,0,0,1,0], [1,0,0,1,1], [1,0,0,1,2], [1,0,0,2,0], [1,0,1,0,0],
  [1,0,1,0,1], [1,0,1,0,2], [1,0,1,1,0], [1,0,1,1,1], [1,0,1,1,2],
  [1,0,1,2,0], [1,0,2,0,0], [1,0,2,0,1], [1,1,0,0,0], [1,1,0,0,1],
  [1,1,0,0,2], [1,1,0,1,0], [1,1,0,1,1], [1,1,0,1,2], [1,1,0,2,0],
  [1,1,1,0,0], [1,1,1,0,1], [1,1,1,0,2], [1,1,1,1,0], [1,1,1,1,1],
  [1,1,1,1,2], [1,1,1,2,0], [1,1,2,0,0], [1,1,2,0,1], [1,2,0,0,0],
  [1,2,0,0,1], [1,2,0,0,2], [1,2,0,1,0], [1,2,0,1,1], [2,0,0,0,0],
  [2,0,0,0,1], [2,0,0,0,2], [2,0,0,1,0], [2,0,0,1,1], [2,0,0,1,2],
  [2,0,0,2,0], [2,0,1,0,0], [2,0,1,0,1], [2,0,1,0,2], [2,0,1,1,0]]

theorem beta13_names_five_eq_certificate :
    beta13Names 5 = beta13NamesFiveCertificate := by decide

def beta13SixGapDifferenceCertificate : List Beta13Code :=
  beta13AdjacentCodeDifferences
    ((beta13NameStep beta13NamesFiveCertificate).map beta13NormalizedNameCode)

def beta13FiveGapCodes : Finset Beta13Code :=
  {(1,0), (-2,1), (3,-1), (-4,2), (5,-2)}

def beta13SixGapCodes : Finset Beta13Code :=
  {(1,0), (-2,1), (3,-1), (-4,2), (5,-2), (-6,3)}

theorem beta13_six_gap_chunk_zero :
    (beta13SixGapDifferenceCertificate.take 50).toFinset = beta13FiveGapCodes := by decide

theorem beta13_six_gap_chunk_one :
    ((beta13SixGapDifferenceCertificate.drop 50).take 50).toFinset = beta13SixGapCodes := by
  decide

theorem beta13_six_gap_chunk_two :
    ((beta13SixGapDifferenceCertificate.drop 100).take 50).toFinset =
      beta13FiveGapCodes := by
  decide

theorem beta13_six_gap_chunk_three :
    (beta13SixGapDifferenceCertificate.drop 150).toFinset = beta13SixGapCodes := by decide

theorem beta13_six_gap_difference_certificate :
    beta13SixGapDifferenceCertificate.toFinset = beta13SixGapCodes := by
  rw [← List.take_append_drop 50 beta13SixGapDifferenceCertificate, List.toFinset_append,
    beta13_six_gap_chunk_zero]
  rw [← List.take_append_drop 50 (beta13SixGapDifferenceCertificate.drop 50),
    List.toFinset_append, beta13_six_gap_chunk_one]
  norm_num only [List.drop_drop]
  rw [← List.take_append_drop 50 (beta13SixGapDifferenceCertificate.drop 100),
    List.toFinset_append, beta13_six_gap_chunk_two]
  norm_num only [List.drop_drop]
  rw [beta13_six_gap_chunk_three]
  decide

/-- The new infinite-prefix model independently has six normalized gap types at level six. -/
theorem beta13_infinite_gap_type_count_six :
    (beta13NormalizedGapSpectrum 6).card = 6 := by
  rw [beta13NormalizedGapSpectrum,
    Finset.card_image_of_injective _ beta13_code_value_injective]
  have hnames : beta13Names 6 = beta13NameStep beta13NamesFiveCertificate := by
    rw [show beta13Names 6 = beta13NameStep (beta13Names 5) by rfl,
      beta13_names_five_eq_certificate]
  rw [beta13NormalizedGapCodes, hnames]
  change beta13SixGapDifferenceCertificate.toFinset.card = 6
  rw [beta13_six_gap_difference_certificate]
  decide

end D5.S0.Tower.NonPisot.Beta13Infinite

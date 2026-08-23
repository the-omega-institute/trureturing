/- GID: D5/S1/Words/NegativeExpansions/BasePhiNegativeTailWords
   generality: I
   mirror-B: none(waiver:negative-tail-word-support)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Finite shallow words realize complete canonical negative base-phi tails. -/

import D5.S1.Words.NegativeExpansions.NegaFibonacci
import D5.S1.Words.NegativeExpansions.BasePhiNegativePrefixTridentTrace

namespace D5.S1.Words.NegativeExpansions.BasePhiNegativeTailWords

open D5.S0.Carrier
open D5.S1.Scale
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiRecursiveStructure
open D5.S1.Words.Expansions.BasePhiTailBounds
open D5.S1.Words.NegativeExpansions.NegaFibonacci

noncomputable section

/-- A shallow-first finite word placed at exponents `-1,-2,...`. -/
noncomputable def wordDigits : List Nat → Int →₀ Nat
  | [] => 0
  | digit :: tail =>
      Finsupp.single (-1) digit + shiftDigits (-1) (wordDigits tail)

@[simp] theorem wordDigits_nil : wordDigits [] = 0 := rfl

theorem wordDigits_nonnegative : ∀ (word : List Nat) (i : Int),
    0 ≤ i → wordDigits word i = 0
  | [], _, _ => by simp [wordDigits]
  | digit :: tail, i, hi => by
      rw [wordDigits, Finsupp.add_apply, Finsupp.single_apply,
        shiftDigits_apply]
      have hne : i ≠ -1 := by omega
      rw [if_neg (Ne.symm hne)]
      simpa using wordDigits_nonnegative tail (i - -1) (by omega)

@[simp] theorem wordDigits_zero (word : List Nat) : wordDigits word 0 = 0 :=
  wordDigits_nonnegative word 0 (by omega)

theorem wordDigits_binary : ∀ {word : List Nat},
    Canonical word → ∀ i : Int, wordDigits word i ≤ 1
  | [], _, i => by simp [wordDigits]
  | digit :: tail, hcanonical, i => by
      by_cases hi : i = -1
      · subst i
        rw [wordDigits, Finsupp.add_apply, Finsupp.single_eq_same,
          shiftDigits_apply]
        norm_num
        exact hcanonical.1
      · by_cases hdeep : i < -1
        · rw [wordDigits, Finsupp.add_apply, Finsupp.single_apply,
            if_neg (Ne.symm hi), zero_add, shiftDigits_apply]
          exact wordDigits_binary hcanonical.2.2 (i - -1)
        · have hinonnegative : 0 ≤ i := by omega
          rw [wordDigits_nonnegative (digit :: tail) i hinonnegative]
          omega

theorem wordDigits_apply_neg : ∀ (word : List Nat) (k : Nat),
    wordDigits word (-((k + 1 : Nat) : Int)) = word.getD k 0
  | [], k => by simp [wordDigits]
  | digit :: tail, 0 => by
      norm_num
      rw [wordDigits, Finsupp.add_apply, Finsupp.single_eq_same,
        shiftDigits_apply]
      norm_num
  | digit :: tail, k + 1 => by
      rw [wordDigits, Finsupp.add_apply, Finsupp.single_apply]
      have hne : -(((k + 1) + 1 : Nat) : Int) ≠ -1 := by omega
      rw [if_neg (Ne.symm hne), zero_add, shiftDigits_apply]
      convert wordDigits_apply_neg tail k using 1 <;> simp

theorem wordDigits_deepest {word : List Nat} {digit : Nat}
    (hlast : word.getLast? = some digit) :
    wordDigits word (-(word.length : Int)) = digit := by
  have hnonempty : word ≠ [] := by
    intro hzero
    subst word
    simp at hlast
  have hlength : word.length ≠ 0 := by
    intro hzero
    exact hnonempty (List.eq_nil_of_length_eq_zero hzero)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hlength
  have hlastIndex : word[k]? = some digit := by
    rw [← show word.length - 1 = k by omega,
      ← List.getLast?_eq_getElem?]
    exact hlast
  rw [hk]
  simpa [List.getD_eq_getElem?_getD, hlastIndex] using wordDigits_apply_neg word k

theorem wordDigits_append (left right : List Nat) :
    wordDigits (left ++ right) =
      wordDigits left + shiftDigits (-(left.length : Int)) (wordDigits right) := by
  induction left with
  | nil =>
      ext i
      simp [wordDigits, shiftDigits_apply]
  | cons digit tail ih =>
      calc
        wordDigits ((digit :: tail) ++ right) =
            Finsupp.single (-1) digit +
              shiftDigits (-1) (wordDigits (tail ++ right)) := rfl
        _ = Finsupp.single (-1) digit +
              shiftDigits (-1) (wordDigits tail +
                shiftDigits (-(tail.length : Int)) (wordDigits right)) := by rw [ih]
        _ = wordDigits (digit :: tail) +
              shiftDigits (-((digit :: tail).length : Int)) (wordDigits right) := by
          rw [shiftDigits_add]
          ext i
          simp only [wordDigits, Finsupp.add_apply, shiftDigits_apply,
            List.length_cons]
          have hindex : i - -1 - -(tail.length : Int) =
              i - -((tail.length + 1 : Nat) : Int) := by
            push_cast
            ring
          rw [hindex]
          simp [Nat.add_assoc]

theorem wordDigits_canonical : ∀ {word : List Nat},
    Canonical word → ∀ i : Int,
      wordDigits word i = 1 → wordDigits word (i + 1) = 0
  | [], _, i => by simp [wordDigits]
  | digit :: tail, hcanonical, i => by
      by_cases hi : i = -1
      · subst i
        norm_num [wordDigits_nonnegative]
      · by_cases hdeep : i < -1
        · have hnextShift : i + 1 - -1 = (i - -1) + 1 := by ring
          rw [wordDigits, Finsupp.add_apply, Finsupp.single_apply,
            if_neg (Ne.symm hi),
            zero_add, shiftDigits_apply]
          intro hone
          by_cases hboundary : i = -2
          · subst i
            have hcurrent : digit = 0 := by
              cases tail with
              | nil => simp [wordDigits] at hone
              | cons next rest =>
                  have hnextOne : next = 1 := by
                    have happly := wordDigits_apply_neg (next :: rest) 0
                    norm_num at happly
                    norm_num at hone
                    rw [happly] at hone
                    exact hone
                  by_cases hdigit : digit = 0
                  · exact hdigit
                  · have hdigitOne : digit = 1 := by have := hcanonical.1; omega
                    have hnextZero := hcanonical.2.1 hdigitOne
                    omega
            subst digit
            simp
          · rw [Finsupp.add_apply, Finsupp.single_apply]
            have hnextNe : i + 1 ≠ -1 := by omega
            rw [if_neg (Ne.symm hnextNe), zero_add, shiftDigits_apply, hnextShift]
            exact wordDigits_canonical hcanonical.2.2 (i - -1) hone
        · have hinonnegative : 0 ≤ i := by omega
          rw [wordDigits_nonnegative (digit :: tail) i hinonnegative]
          simp

private theorem basePhiValue_eq_sum (digits : Int →₀ Nat) :
    basePhiValue digits = digits.sum (fun i coefficient =>
      (coefficient : GoldenInt) *
        (((phiUnit ^ i : GoldenIntˣ) : GoldenInt))) := by
  rfl

private theorem basePhiValue_single (i : Int) (coefficient : Nat) :
    basePhiValue (Finsupp.single i coefficient) =
      (coefficient : GoldenInt) *
        (((phiUnit ^ i : GoldenIntˣ) : GoldenInt)) := by
  classical
  rw [basePhiValue_eq_sum, Finsupp.sum_single_index]
  simp

private theorem negative_phiUnit_local (K : Nat) :
    (((phiUnit ^ (-(K : Int)) : GoldenIntˣ) : GoldenInt)) =
      (-conj phi) ^ K := by
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  rfl

private theorem negative_phiUnit_one :
    (((phiUnit ^ (-1 : Int) : GoldenIntˣ) : GoldenInt)) = ⟨-1, 1⟩ := by
  rw [show (-1 : Int) = -((1 : Nat) : Int) by norm_num,
    negative_phiUnit_local]
  apply GoldenInt.ext <;> norm_num [conj, phi]

theorem negative_phiUnit_coordinates (K : Nat) :
    let value := (((phiUnit ^ (-(K : Int)) : GoldenIntˣ) : GoldenInt))
    value.a = (-1 : Int) ^ K * Nat.fib (K + 1) ∧
      value.b = (-1 : Int) ^ (K + 1) * Nat.fib K := by
  induction K with
  | zero => norm_num [phiUnit]
  | succ K ih =>
      dsimp at ih ⊢
      rw [show -(↑K + 1 : Int) = -(K : Int) + (-1 : Int) by ring,
        zpow_add, Units.val_mul, negative_phiUnit_one]
      constructor
      · simp only [a_mul]
        rw [ih.1, ih.2, pow_succ]
        rw [show K + 1 + 1 = K + 2 by omega, Nat.fib_add_two]
        push_cast
        ring
      · simp only [b_mul]
        rw [ih.1, ih.2, pow_succ]
        ring

private theorem wordDigits_value_cons (digit : Nat) (tail : List Nat) :
    basePhiValue (wordDigits (digit :: tail)) =
      (digit : GoldenInt) * ⟨-1, 1⟩ +
        ⟨-1, 1⟩ * basePhiValue (wordDigits tail) := by
  rw [wordDigits, basePhiValue_add, basePhiValue_single, shiftDigits_eval,
    negative_phiUnit_one]

private theorem shifted_single_b (digit K : Nat) :
    (basePhiValue
      (shiftDigits (-(K : Int)) (wordDigits [digit]))).b =
        (digit : Int) * (-1 : Int) ^ K * Nat.fib (K + 1) := by
  rw [shiftDigits_eval, wordDigits_value_cons]
  have hzero : basePhiValue (wordDigits []) = 0 := by
    simp [wordDigits, basePhiValue]
  rw [hzero, mul_zero, add_zero]
  simp only [b_mul, a_natCast, b_natCast, a_mul]
  have hcoordinates := negative_phiUnit_coordinates K
  dsimp at hcoordinates
  rw [hcoordinates.1, hcoordinates.2]
  push_cast
  rw [pow_succ]
  ring

/-- The alternating Fibonacci word weight is the negated golden coordinate
of the corresponding shallow negative tail. -/
theorem reverse_weight_eq_neg_b : ∀ digits : List Nat,
    weight digits = -(basePhiValue (wordDigits digits.reverse)).b
  | [] => by simp [weight, basePhiValue]
  | digit :: tail => by
      rw [weight, List.reverse_cons, wordDigits_append, basePhiValue_add, b_add,
        reverse_weight_eq_neg_b tail, shifted_single_b]
      simp only [List.length_reverse]
      rw [pow_succ]
      ring

noncomputable def realValue : List Nat → Real
  | [] => 0
  | digit :: tail => Real.goldenRatio⁻¹ * (digit + realValue tail)

theorem embedding_wordDigits : ∀ word : List Nat,
    embedding (basePhiValue (wordDigits word)) = realValue word
  | [] => by simp [wordDigits, basePhiValue, realValue]
  | digit :: tail => by
      rw [wordDigits_value_cons, map_add, map_mul, map_mul,
        embedding_wordDigits tail]
      simp only [embedding_apply, a_natCast, b_natCast]
      have hinverse : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
        rw [Real.inv_goldenRatio]
        ring
      rw [realValue, hinverse]
      push_cast
      ring

private theorem inverse_pos : 0 < Real.goldenRatio⁻¹ :=
  inv_pos.mpr Real.goldenRatio_pos

private theorem inverse_lt_one : Real.goldenRatio⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

private theorem inverse_add_sq :
    Real.goldenRatio⁻¹ + Real.goldenRatio⁻¹ ^ 2 = 1 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

private theorem realValue_bounds : ∀ {word : List Nat},
    Canonical word → 0 ≤ realValue word ∧ realValue word < 1
  | [], _ => by simp [realValue]
  | digit :: tail, hcanonical => by
      have htail := realValue_bounds hcanonical.2.2
      have hdigit : digit = 0 ∨ digit = 1 := by have := hcanonical.1; omega
      rcases hdigit with rfl | rfl
      · simp only [realValue, Nat.cast_zero, zero_add]
        constructor
        · exact mul_nonneg inverse_pos.le htail.1
        · exact (mul_lt_of_lt_one_right inverse_pos htail.2).trans inverse_lt_one
      · cases tail with
        | nil =>
            simp only [realValue, Nat.cast_one, add_zero]
            simpa only [mul_one] using And.intro inverse_pos.le inverse_lt_one
        | cons next rest =>
            have hnext : next = 0 := hcanonical.2.1 rfl
            subst next
            have hrest := realValue_bounds hcanonical.2.2.2.2
            simp only [realValue, Nat.cast_one, Nat.cast_zero, zero_add]
            constructor
            · exact mul_nonneg inverse_pos.le
                (add_nonneg zero_le_one (mul_nonneg inverse_pos.le hrest.1))
            · have hscaled : Real.goldenRatio⁻¹ ^ 2 * realValue rest <
                  Real.goldenRatio⁻¹ ^ 2 :=
                mul_lt_of_lt_one_right (sq_pos_of_pos inverse_pos) hrest.2
              nlinarith [inverse_add_sq]

private theorem realValue_pos_of_last_one : ∀ {word : List Nat},
    Canonical word → word.getLast? = some 1 → 0 < realValue word
  | [], _, hlast => by simp at hlast
  | digit :: tail, hcanonical, hlast => by
      cases tail with
      | nil =>
          have hdigit : digit = 1 := by simpa using hlast
          subst digit
          simpa [realValue] using inverse_pos
      | cons next rest =>
          have htailPos := realValue_pos_of_last_one hcanonical.2.2 (by simpa using hlast)
          have hdigitNonnegative : (0 : Real) ≤ digit := by positivity
          simp only [realValue]
          exact mul_pos inverse_pos
            (add_pos_of_nonneg_of_pos hdigitNonnegative htailPos)

theorem positive_word_coordinates {digits : List Nat} {value : Nat}
    (hcanonical : Canonical digits)
    (hhead : digits.head? = some 1)
    (hweight : weight digits = value)
    (_hvalue : 0 < value) :
    let tail := basePhiValue (wordDigits digits.reverse)
    tail.b = -(value : Int) ∧
      tail.a = ⌊(value : Real) * Real.goldenRatio⌋ + 1 ∧
      trace tail = 2 * ⌊(value : Real) * Real.goldenRatio⌋ - value + 2 := by
  let tail := basePhiValue (wordDigits digits.reverse)
  change tail.b = -(value : Int) ∧
    tail.a = ⌊(value : Real) * Real.goldenRatio⌋ + 1 ∧
    trace tail = 2 * ⌊(value : Real) * Real.goldenRatio⌋ - value + 2
  have hb : tail.b = -(value : Int) := by
    have := reverse_weight_eq_neg_b digits
    rw [hweight] at this
    dsimp [tail]
    omega
  have hreverseCanonical := canonical_reverse hcanonical
  have hlast : digits.reverse.getLast? = some 1 := by
    simpa using hhead
  have hrealPos : 0 < embedding tail := by
    rw [show embedding tail = realValue digits.reverse by
      exact embedding_wordDigits digits.reverse]
    exact realValue_pos_of_last_one hreverseCanonical hlast
  have hrealLt : embedding tail < 1 := by
    rw [show embedding tail = realValue digits.reverse by
      exact embedding_wordDigits digits.reverse]
    exact (realValue_bounds hreverseCanonical).2
  have hformula : embedding tail =
      (tail.a : Real) - (value : Real) * Real.goldenRatio := by
    rw [embedding_apply, hb]
    push_cast
    ring
  have hfloor : ⌊(value : Real) * Real.goldenRatio⌋ = tail.a - 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · rw [hformula] at hrealPos
      norm_num only [Int.cast_sub, Int.cast_one]
      linarith
    · rw [hformula] at hrealPos
      norm_num only [Int.cast_sub, Int.cast_one, sub_add_cancel]
      linarith
  refine ⟨hb, (by omega), ?_⟩
  simp only [trace]
  omega

theorem negative_word_coordinates {digits : List Nat} {value : Nat}
    (hcanonical : Canonical digits)
    (hhead : digits.head? = some 1)
    (hweight : weight digits = -(value : Int))
    (_hvalue : 0 < value) :
    let tail := basePhiValue (wordDigits digits.reverse)
    tail.b = (value : Int) ∧
      tail.a = -⌊(value : Real) * Real.goldenRatio⌋ ∧
      trace tail = -2 * ⌊(value : Real) * Real.goldenRatio⌋ + value := by
  let tail := basePhiValue (wordDigits digits.reverse)
  change tail.b = (value : Int) ∧
    tail.a = -⌊(value : Real) * Real.goldenRatio⌋ ∧
    trace tail = -2 * ⌊(value : Real) * Real.goldenRatio⌋ + value
  have hb : tail.b = (value : Int) := by
    have := reverse_weight_eq_neg_b digits
    rw [hweight] at this
    dsimp [tail]
    omega
  have hreverseCanonical := canonical_reverse hcanonical
  have hlast : digits.reverse.getLast? = some 1 := by simpa using hhead
  have hrealPos : 0 < embedding tail := by
    rw [show embedding tail = realValue digits.reverse by
      exact embedding_wordDigits digits.reverse]
    exact realValue_pos_of_last_one hreverseCanonical hlast
  have hrealLt : embedding tail < 1 := by
    rw [show embedding tail = realValue digits.reverse by
      exact embedding_wordDigits digits.reverse]
    exact (realValue_bounds hreverseCanonical).2
  have hformula : embedding tail =
      (tail.a : Real) + (value : Real) * Real.goldenRatio := by
    rw [embedding_apply, hb]
    push_cast
    ring
  have hfloor : ⌊(value : Real) * Real.goldenRatio⌋ = -tail.a := by
    apply Int.floor_eq_iff.mpr
    constructor
    · rw [hformula] at hrealPos
      norm_num only [Int.cast_neg]
      linarith
    · rw [hformula] at hrealLt
      norm_num only [Int.cast_add, Int.cast_neg, Int.cast_one]
      linarith
  refine ⟨hb, (by omega), ?_⟩
  simp only [trace]
  omega

private theorem inverse_le_realValue_of_head_one (tail : List Nat) :
    Real.goldenRatio⁻¹ ≤ realValue (1 :: tail) := by
  have hnonnegative : 0 ≤ realValue tail := by
    induction tail with
    | nil => simp [realValue]
    | cons digit rest ih => simp only [realValue]; positivity
  simp only [realValue, Nat.cast_one]
  nlinarith [inverse_pos]

private theorem realValue_lt_inverse_of_head_zero {tail : List Nat}
    (hcanonical : Canonical (0 :: tail)) :
    realValue (0 :: tail) < Real.goldenRatio⁻¹ := by
  have htail := realValue_bounds hcanonical.2.2
  simp only [realValue, Nat.cast_zero, zero_add]
  nlinarith [inverse_pos]

/-- A nonempty canonical shallow word with integral trace above one realizes
the first point of its complete negative-tail fiber. -/
theorem fiberStart_of_word {word : List Nat}
    (hcanonical : Canonical word)
    (hlast : word.getLast? = some 1)
    (htrace : 1 < trace (basePhiValue (wordDigits word))) :
    let q := (trace (basePhiValue (wordDigits word)) - 1).toNat
    D5.X_Frontier.BasePhiNegativePrefixTrident.fiberStart q ∧
      negativePart
          D5.X_Frontier.BasePhiNegativePrefixTrident.canonicalExpansion q =
        wordDigits word := by
  have h := D5.X_Frontier.BasePhiNegativePrefixTrident.fiberStart_of_complete_tail
    (wordDigits word) (wordDigits_nonnegative word)
    (wordDigits_binary hcanonical) (wordDigits_canonical hcanonical)
    (by rw [embedding_wordDigits]; exact realValue_pos_of_last_one hcanonical hlast)
    (by rw [embedding_wordDigits]; exact (realValue_bounds hcanonical).2)
    (by
      intro hone
      cases word with
      | nil => simp [wordDigits] at hone
      | cons digit tail =>
          have hdigit : digit = 1 := by
            have happly := wordDigits_apply_neg (digit :: tail) 0
            norm_num at happly
            omega
          subst digit
          rw [embedding_wordDigits]
          exact inverse_le_realValue_of_head_one tail)
    (by
      intro hzero
      cases word with
      | nil => simp at hlast
      | cons digit tail =>
          have hdigit : digit = 0 := by
            have hdigitLe := hcanonical.1
            have happly := wordDigits_apply_neg (digit :: tail) 0
            norm_num at happly
            omega
          subst digit
          rw [embedding_wordDigits]
          exact realValue_lt_inverse_of_head_zero hcanonical)
    htrace
  refine ⟨h.1, ?_⟩
  apply bilateral_basePhi_injective
    (negativePart_binary _ _) (negativePart_canonical _ _)
    (wordDigits_binary hcanonical) (wordDigits_canonical hcanonical)
  exact h.2

end

end D5.S1.Words.NegativeExpansions.BasePhiNegativeTailWords

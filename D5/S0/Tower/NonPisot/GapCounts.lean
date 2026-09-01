/- GID: D5/S0/Tower/NonPisot/GapCounts
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisot/GapCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact greedy beta-shift normalized gap-type counts at levels six, eight, and ten. -/

import D5.S0.Tower.NonPisot.Beta13
import D5.S0.Tower.Tribonacci.Gaps

namespace D5.S0.Tower.NonPisot.GapCounts

/- A code `(a, b)` denotes the exact real number `a + b * beta13`. -/
abbrev Beta13GapCode := Int × Int

/-- Multiplication by `beta13`, reduced with `beta13^2 = beta13 + 3`. -/
def beta13CodeMul (code : Beta13GapCode) : Beta13GapCode :=
  (3 * code.2, code.1 + code.2)

/-- Add a nonnegative digit to an exact normalized name value. -/
def beta13CodeAddDigit (code : Beta13GapCode) (digit : Nat) : Beta13GapCode :=
  (code.1 + digit, code.2)

/-- Difference of two exact quadratic codes. -/
def beta13CodeSub (left right : Beta13GapCode) : Beta13GapCode :=
  (left.1 - right.1, left.2 - right.2)

/-- Real interpretation of an exact quadratic code. -/
noncomputable def beta13GapCodeValue (code : Beta13GapCode) : Real :=
  (code.1 : Real) + (code.2 : Real) *
    D5.S0.Tower.NonPisot.Beta13.beta13

/-- The quadratic reduction implements multiplication by the real base. -/
theorem beta13_gap_code_value_mul (code : Beta13GapCode) :
    beta13GapCodeValue (beta13CodeMul code) =
      D5.S0.Tower.NonPisot.Beta13.beta13 * beta13GapCodeValue code := by
  rw [beta13GapCodeValue, beta13GapCodeValue, beta13CodeMul]
  push_cast
  ring_nf
  rw [D5.S0.Tower.NonPisot.Beta13.beta13_sq]
  ring

/-- Distinct integral codes have distinct real values. -/
theorem beta13_gap_code_value_injective : Function.Injective beta13GapCodeValue := by
  intro left right hvalue
  by_cases hsecond : left.2 = right.2
  · have hfirstReal : (left.1 : Real) = (right.1 : Real) := by
      rw [beta13GapCodeValue, beta13GapCodeValue, hsecond] at hvalue
      linarith
    have hfirst : left.1 = right.1 := by exact_mod_cast hfirstReal
    exact Prod.ext hfirst hsecond
  · exfalso
    apply D5.S0.Tower.NonPisot.Beta13.beta13_irrational.ne_rational
      (right.1 - left.1) (left.2 - right.2)
    field_simp [sub_ne_zero.mpr hsecond]
    rw [beta13GapCodeValue, beta13GapCodeValue] at hvalue
    push_cast at hvalue ⊢
    nlinarith

/-- The first ten greedy digits of one for `beta13`; no later digit is defined here. -/
def beta13GreedyDigits : List Nat := [2, 0, 1, 1, 0, 2, 0, 0, 1, 0]

/-- One exact greedy-remainder step after the chosen digit is removed. -/
def beta13NextRemainderCode (code : Beta13GapCode) (digit : Int) : Beta13GapCode :=
  ((beta13CodeMul code).1 - digit, (beta13CodeMul code).2)

/-- The eleven remainders determined by the initial value and the first ten digits. -/
def beta13RemainderCodes : List Beta13GapCode :=
  List.scanl beta13NextRemainderCode (1, 0) (beta13GreedyDigits.map Int.ofNat)

/-- Exact real compatibility of a remainder step with the beta transformation. -/
theorem beta13_gap_code_value_next (code : Beta13GapCode) (digit : Int) :
    beta13GapCodeValue (beta13NextRemainderCode code digit) =
      D5.S0.Tower.NonPisot.Beta13.beta13 * beta13GapCodeValue code - digit := by
  rw [beta13GapCodeValue, beta13GapCodeValue, beta13NextRemainderCode,
    beta13CodeMul]
  push_cast
  ring_nf
  rw [D5.S0.Tower.NonPisot.Beta13.beta13_sq]
  ring

/-- The displayed digits really are the first ten greedy digits, certified by floors. -/
theorem beta13_first_ten_digits_are_greedy :
    List.Forall₂
      (fun code digit =>
        ⌊D5.S0.Tower.NonPisot.Beta13.beta13 * beta13GapCodeValue code⌋ = digit)
      (beta13RemainderCodes.take 10) (beta13GreedyDigits.map Int.ofNat) := by
  have hsqrt : Real.sqrt (13 : Real) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 <= Real.sqrt (13 : Real) := Real.sqrt_nonneg 13
  have hsqrtLower : (18 : Real) / 5 < Real.sqrt 13 := by nlinarith
  have hsqrtUpper : Real.sqrt 13 < (37 : Real) / 10 := by nlinarith
  rw [show beta13RemainderCodes =
    [(1, 0), (-2, 1), (3, -1), (-4, 2), (5, -2), (-6, 3),
      (7, -3), (-9, 4), (12, -5), (-16, 7), (21, -9)] by decide]
  simp only [beta13GreedyDigits, List.map, List.take, List.forall₂_cons,
    List.forall₂_nil_left_iff]
  repeat' apply And.intro
  all_goals first | trivial | apply Int.floor_eq_iff.mpr
  all_goals constructor <;>
    norm_num [beta13GapCodeValue, D5.S0.Tower.NonPisot.Beta13.beta13] <;>
    nlinarith

/-- The ten post-digit remainders stay in the half-open unit interval. -/
theorem beta13_first_ten_remainders_in_unit_interval :
    (beta13RemainderCodes.drop 1).Forall
      (fun code => 0 <= beta13GapCodeValue code ∧ beta13GapCodeValue code < 1) := by
  have hsqrt : Real.sqrt (13 : Real) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 <= Real.sqrt (13 : Real) := Real.sqrt_nonneg 13
  have hsqrtLower : (18 : Real) / 5 < Real.sqrt 13 := by nlinarith
  have hsqrtUpper : Real.sqrt 13 < (37 : Real) / 10 := by nlinarith
  rw [show beta13RemainderCodes =
    [(1, 0), (-2, 1), (3, -1), (-4, 2), (5, -2), (-6, 3),
      (7, -3), (-9, 4), (12, -5), (-16, 7), (21, -9)] by decide]
  simp only [List.drop, List.forall_cons]
  repeat' apply And.intro
  all_goals first
    | trivial
    | (norm_num [beta13GapCodeValue, D5.S0.Tower.NonPisot.Beta13.beta13]
       nlinarith)

/-- Whether one word is at most the matching certified greedy prefix. -/
def beta13BelowGreedyPrefix (word : List Nat) : Bool :=
  compare word (beta13GreedyDigits.take word.length) != .gt

/-- The length-`Q` greedy-admissible names, generated in lexicographic order.

The tail already has every proper suffix certified at the preceding level, so the recursive
step needs to test only the newly formed full word. -/
def beta13Names : Nat -> List (List Nat)
  | 0 => [[]]
  | Q + 1 => [0, 1, 2].flatMap fun digit =>
      (beta13Names Q).filterMap fun tail =>
        let word := digit :: tail
        if beta13BelowGreedyPrefix word then some word else none

/-- Equivalent ordered generation, stopping after the admissible initial part of the top block. -/
def beta13OrderedNames : Nat -> List (List Nat)
  | 0 => [[]]
  | Q + 1 =>
      let tails := beta13OrderedNames Q
      tails.map (0 :: ·) ++ tails.map (1 :: ·) ++
        (tails.takeWhile fun tail => beta13BelowGreedyPrefix (2 :: tail)).map (2 :: ·)

set_option maxRecDepth 100000 in
/-- At level ten the ordered generator is exactly the suffix-tested greedy generator. -/
theorem beta13_names_ten_eq_ordered : beta13Names 10 = beta13OrderedNames 10 := by
  decide

/-- The code for `beta13^Q` times the value of a length-`Q` name. -/
def beta13NormalizedNameCode (word : List Nat) : Beta13GapCode :=
  word.foldl
    (fun code digit => beta13CodeAddDigit (beta13CodeMul code) digit) (0, 0)

/-- Differences between consecutive entries of an exact ordered code list. -/
def beta13AdjacentCodeDifferences : List Beta13GapCode -> List Beta13GapCode
  | left :: right :: rest =>
      beta13CodeSub right left :: beta13AdjacentCodeDifferences (right :: rest)
  | _ => []

/-- Exact normalized internal adjacent-gap types at level `Q`. -/
def beta13NormalizedGapCodes (Q : Nat) : Finset Beta13GapCode :=
  (beta13AdjacentCodeDifferences
    ((beta13Names Q).map beta13NormalizedNameCode)).toFinset

/-- The standard greedy-remainder candidate types seen through level `Q`. -/
def beta13RemainderSpectrum (Q : Nat) : Finset Beta13GapCode :=
  (beta13RemainderCodes.take Q).toFinset

/-- The exact code spectrum has cardinality six at level six. -/
theorem beta13_normalized_gap_code_count_six :
    (beta13NormalizedGapCodes 6).card = 6 := by
  set_option maxRecDepth 100000 in
    decide

/-- The exact code spectrum has cardinality eight at level eight. -/
theorem beta13_normalized_gap_code_count_eight :
    (beta13NormalizedGapCodes 8).card = 8 := by
  set_option maxRecDepth 100000 in
    decide

set_option maxRecDepth 100000 in
/-- The exact code spectrum has cardinality ten at level ten. -/
theorem beta13_normalized_gap_code_count_ten :
    (beta13NormalizedGapCodes 10).card = 10 := by
  let differences := beta13AdjacentCodeDifferences
    ((beta13OrderedNames 10).map beta13NormalizedNameCode)
  have hforward : differences.Forall (· ∈ beta13RemainderSpectrum 10) := by
    set_option maxRecDepth 100000 in
      decide
  have hbackward : (beta13RemainderCodes.take 10).Forall (· ∈ differences) := by
    set_option maxRecDepth 100000 in
      decide
  have hspectrum : beta13NormalizedGapCodes 10 = beta13RemainderSpectrum 10 := by
    apply Finset.ext
    intro code
    rw [beta13NormalizedGapCodes, beta13_names_ten_eq_ordered, beta13RemainderSpectrum]
    simp only [List.mem_toFinset]
    constructor
    · exact List.forall_iff_forall_mem.mp hforward code
    · exact List.forall_iff_forall_mem.mp hbackward code
  rw [hspectrum]
  decide

/-- The real normalized internal adjacent-gap spectrum. -/
noncomputable def beta13NormalizedGapSpectrum (Q : Nat) : Finset Real :=
  (beta13NormalizedGapCodes Q).image beta13GapCodeValue

/-- There are exactly six normalized internal adjacent-gap types at level six. -/
theorem beta13_normalized_gap_type_count_six :
    (beta13NormalizedGapSpectrum 6).card = 6 := by
  rw [beta13NormalizedGapSpectrum,
    Finset.card_image_of_injective _ beta13_gap_code_value_injective]
  exact beta13_normalized_gap_code_count_six

/-- There are exactly eight normalized internal adjacent-gap types at level eight. -/
theorem beta13_normalized_gap_type_count_eight :
    (beta13NormalizedGapSpectrum 8).card = 8 := by
  rw [beta13NormalizedGapSpectrum,
    Finset.card_image_of_injective _ beta13_gap_code_value_injective]
  exact beta13_normalized_gap_code_count_eight

/-- There are exactly ten normalized internal adjacent-gap types at level ten. -/
theorem beta13_normalized_gap_type_count_ten :
    (beta13NormalizedGapSpectrum 10).card = 10 := by
  rw [beta13NormalizedGapSpectrum,
    Finset.card_image_of_injective _ beta13_gap_code_value_injective]
  exact beta13_normalized_gap_code_count_ten

/-- The frozen Tribonacci adjacent-gap spectrum has cardinality three at every level from three. -/
theorem tribonacci_normalized_gap_type_count (Q : Nat) (hQ : 3 <= Q) :
    (D5.S0.Tower.Tribonacci.Gaps.adjacentGapSpectrum Q).card = 3 :=
  D5.S0.Tower.Tribonacci.Gaps.adjacent_gap_spectrum_card Q hQ

end D5.S0.Tower.NonPisot.GapCounts

/- GID: D5/S3/Observer/GoldenChronology/GoldenMagnusParityRecovery
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Magnus center recovers fixed-length golden factors exactly at even lengths. -/

import D5.S3.Observer.GoldenChronology.GoldenFactorParikhMagnusBridge
import D5.S1.Words.Palindromes.GoldenPalindromicFactorComplexity

/-!
# Window parity controls the minimal golden chronology readout

The readout is the actual central coordinate of the existing represented
second Magnus signature, not a separately attached statistic. Balance allows
only consecutive true counts at one length. At even lengths the center's
parity distinguishes those counts, so the count coordinate is recoverable.
At every odd length the two distinct palindromic factors have center zero.
Consequently center-only factor recovery holds exactly at even lengths.

Every center fiber has at most two word contents. Occurrence indices remain
unrecoverable. This parity concerns word length, not primality, prime-factor
multiplicity, Zeckendorf least-index parity, or Lie degree.

Search receipt: no such center-only parity classification was found in the
pinned repository. The proof reuses golden balance, binomial recovery, and
the frozen exact palindromic-factor complexity; no claim of priority in the
combinatorics literature is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery

open D5.S1.Words
open D5.S1.Words.GoldenRecovery.GoldenFactorSecondOrderBinomialRigidity
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge
open D5.S3.Observer.GoldenChronology.GoldenFactorParikhMagnusBridge

/-- The actual central doubled Magnus coordinate of the fixed binary observer. -/
def magnusCenter (word : List Bool) : ℤ :=
  doubledMagnusDegreeTwo (chronologicalSignature binaryLetterObservation word) 0 2

/-- The coordinate is the difference of the two oriented pair counts. -/
theorem magnus_center_formula (word : List Bool) :
    magnusCenter word = 2 * (scatteredTrueFalseCount word : ℤ) -
      (word.count true : ℤ) * (word.count false : ℤ) :=
  binary_doubled_magnus_center word

/-- Reversal partitions all pairs of unlike letters into the two orientations. -/
theorem scattered_pair_reversal_sum (word : List Bool) :
    scatteredTrueFalseCount word + scatteredTrueFalseCount word.reverse =
      word.count true * word.count false := by
  induction word with
  | nil => simp [scatteredTrueFalseCount]
  | cons letter tail ih =>
      rw [List.reverse_cons, scattered_true_false_count_append_letter]
      cases letter <;>
        simp [scatteredTrueFalseCount, List.count_reverse] at ih ⊢ <;>
        nlinarith

/-- Plain word reversal negates this second-order chronology coordinate. -/
theorem magnus_center_reverse (word : List Bool) :
    magnusCenter word.reverse = -magnusCenter word := by
  have hpairs := scattered_pair_reversal_sum word
  have hcast : (scatteredTrueFalseCount word : ℤ) +
      (scatteredTrueFalseCount word.reverse : ℤ) =
      (word.count true : ℤ) * (word.count false : ℤ) := by
    exact_mod_cast hpairs
  rw [magnus_center_formula, magnus_center_formula]
  simp only [List.count_reverse]
  omega

/-- A reversal-fixed word has zero central second Magnus coordinate. -/
theorem magnus_center_zero_of_reverse_eq (word : List Bool)
    (hpal : word.reverse = word) : magnusCenter word = 0 := by
  have h := magnus_center_reverse word
  rw [hpal] at h
  omega

/-- One count plus the center recovers a factor of known length. -/
theorem golden_factor_eq_of_count_and_center (n i j : ℕ)
    (hr : goldenWindowTrueCount i n = goldenWindowTrueCount j n)
    (hm : magnusCenter (goldenFactor n i) = magnusCenter (goldenFactor n j)) :
    goldenFactor n i = goldenFactor n j := by
  change doubledMagnusDegreeTwo
      (chronologicalSignature binaryLetterObservation (goldenFactor n i)) 0 2 =
    doubledMagnusDegreeTwo
      (chronologicalSignature binaryLetterObservation (goldenFactor n j)) 0 2 at hm
  rw [golden_factor_doubled_magnus_center, golden_factor_doubled_magnus_center, hr] at hm
  apply golden_factor_eq_of_second_order_counts n i j hr
  omega

private theorem even_centered_count_rigidity (n r s p q : ℤ)
    (hn : Even n) (hbalance : |r - s| ≤ 1)
    (hcenter : 2 * p - r * (n - r) = 2 * q - s * (n - s)) : r = s := by
  obtain ⟨k, hk⟩ := hn
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbalance
  by_contra hne
  have hstep : s = r + 1 ∨ r = s + 1 := by omega
  rcases hstep with hstep | hstep
  · rw [hstep] at hcenter
    have hlinear : 2 * p - 2 * q = 2 * r + 1 - n := by
      nlinarith [hcenter]
    omega
  · rw [hstep] at hcenter
    have hlinear : 2 * q - 2 * p = 2 * s + 1 - n := by
      nlinarith [hcenter]
    omega

/-- At even length the Magnus center alone recovers the complete golden factor. -/
theorem even_length_center_recovers_golden_factor (n : ℕ) (hn : Even n) (i j : ℕ)
    (hm : magnusCenter (goldenFactor n i) = magnusCenter (goldenFactor n j)) :
    goldenFactor n i = goldenFactor n j := by
  have hnInt : Even (n : ℤ) := by
    obtain ⟨k, hk⟩ := hn
    refine ⟨(k : ℤ), ?_⟩
    exact_mod_cast hk
  have hformula := hm
  change doubledMagnusDegreeTwo
      (chronologicalSignature binaryLetterObservation (goldenFactor n i)) 0 2 =
    doubledMagnusDegreeTwo
      (chronologicalSignature binaryLetterObservation (goldenFactor n j)) 0 2 at hformula
  rw [golden_factor_doubled_magnus_center,
    golden_factor_doubled_magnus_center] at hformula
  have hcountInt := even_centered_count_rigidity (n : ℤ)
    (goldenWindowTrueCount i n) (goldenWindowTrueCount j n)
    (goldenTrueFalseCount i n) (goldenTrueFalseCount j n)
    hnInt (goldenWord_balanced_one i j n) hformula
  apply golden_factor_eq_of_count_and_center n i j _ hm
  exact_mod_cast hcountInt

/-- At every odd length two distinct legal palindromes give a center collision. -/
theorem odd_length_center_collision (n : ℕ) (hn : Odd n) :
    ∃ i j : ℕ, goldenFactor n i ≠ goldenFactor n j ∧
      magnusCenter (goldenFactor n i) = 0 ∧
      magnusCenter (goldenFactor n j) = 0 := by
  classical
  have hnot : ¬ Even n := Nat.not_even_iff_odd.mpr hn
  have hcard : 1 < (goldenPalindromicFactorSet n).card := by
    rw [golden_palindromic_factor_complexity, if_neg hnot]
    decide
  obtain ⟨left, hleft, right, hright, hne⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨i, hi, hpi⟩ := mem_goldenPalindromicFactorSet.mp hleft
  obtain ⟨j, hj, hpj⟩ := mem_goldenPalindromicFactorSet.mp hright
  refine ⟨i, j, ?_, ?_, ?_⟩
  · intro h
    exact hne (hi.trans (h.trans hj.symm))
  · rw [← hi]
    exact magnus_center_zero_of_reverse_eq left hpi.reverse_eq
  · rw [← hj]
    exact magnus_center_zero_of_reverse_eq right hpj.reverse_eq

/-- Exact parity classification of center-only recovery on the legal language. -/
theorem center_recovers_fixed_length_iff_even (n : ℕ) :
    (∀ i j : ℕ, magnusCenter (goldenFactor n i) = magnusCenter (goldenFactor n j) →
      goldenFactor n i = goldenFactor n j) ↔ Even n := by
  constructor
  · intro h
    by_contra hnot
    obtain ⟨i, j, hne, hi, hj⟩ :=
      odd_length_center_collision n (Nat.not_even_iff_odd.mp hnot)
    exact hne (h i j (hi.trans hj.symm))
  · intro hn
    exact even_length_center_recovers_golden_factor n hn

/-- No central fiber contains three distinct same-length legal word contents. -/
theorem center_fiber_has_at_most_two_words (n i j k : ℕ)
    (hij : magnusCenter (goldenFactor n i) = magnusCenter (goldenFactor n j))
    (hik : magnusCenter (goldenFactor n i) = magnusCenter (goldenFactor n k)) :
    goldenFactor n i = goldenFactor n j ∨
      goldenFactor n i = goldenFactor n k ∨ goldenFactor n j = goldenFactor n k := by
  have hijb := abs_le.mp (goldenWord_balanced_one i j n)
  have hikb := abs_le.mp (goldenWord_balanced_one i k n)
  have hjkb := abs_le.mp (goldenWord_balanced_one j k n)
  have counts : goldenWindowTrueCount i n = goldenWindowTrueCount j n ∨
      goldenWindowTrueCount i n = goldenWindowTrueCount k n ∨
      goldenWindowTrueCount j n = goldenWindowTrueCount k n := by omega
  rcases counts with h | h | h
  · exact Or.inl (golden_factor_eq_of_count_and_center n i j h hij)
  · exact Or.inr (Or.inl (golden_factor_eq_of_count_and_center n i k h hik))
  · exact Or.inr (Or.inr
      (golden_factor_eq_of_count_and_center n j k h (hij.symm.trans hik)))

#print axioms magnus_center_reverse
#print axioms even_length_center_recovers_golden_factor
#print axioms odd_length_center_collision
#print axioms center_recovers_fixed_length_iff_even
#print axioms center_fiber_has_at_most_two_words

end D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery

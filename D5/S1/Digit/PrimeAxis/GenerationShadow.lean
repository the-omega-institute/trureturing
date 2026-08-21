/- GID: D5/S1/Digit/PrimeAxis/GenerationShadow
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxis/GenerationShadow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Multiplication is the decoded shadow of exponent generation, and motion has length. -/

import D5.S1.Digit.PrimeAxis.PrimeAxisNormalizationUnique
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace D5.S1.Digit.PrimeAxis.GenerationShadow

open Real
open D5.S1.Digit

/- The clause reads the kernel's bottom layer as generation on a prime exponent ledger,
`a ↦ a + u`, with integer multiplication appearing only as the decoded image of that motion.
It then records a pointwise lemma for the arrow of time: a nonempty state has positive
length, because some exponent is positive and every prime has positive logarithm.

The decoder and the normalized step already exist. What is added here is the length, which
had no formalization: a search for a state length on prime-axis tables returned nothing. -/

/-- The length of a state: each prime axis contributes its exponent times the prime's
logarithm. -/
noncomputable def stateLength (z : PrimeAxisTable) : ℝ :=
  z.digits.sum fun p row => (rawValue row : ℝ) * Real.log (p : ℕ)

/-- Generation is additive on exponents, so the decoder turns it into multiplication: this
is the sense in which multiplication is a shadow rather than a primitive. -/
theorem decode_generation (z u : PrimeAxisTable) :
    decodePrimeAxisTable (normalizedPrimeAxisAdd z u) =
      decodePrimeAxisTable z * decodePrimeAxisTable u :=
  (prime_axis_addition_spec z u).2

/-- Every prime contributes a positive amount of length. -/
theorem log_prime_pos (p : PrimeAxis) : 0 < Real.log (p : ℕ) := by
  have h2 : (2 : ℕ) ≤ (p : ℕ) := p.2.two_le
  have h1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two h2
  exact Real.log_pos h1

/-- Length is never negative, since every summand is a nonnegative exponent times a positive
logarithm. -/
theorem stateLength_nonneg (z : PrimeAxisTable) : 0 ≤ stateLength z := by
  refine Finset.sum_nonneg ?_
  intro p _
  exact mul_nonneg (by positivity) (le_of_lt (log_prime_pos p))

/-- The pointwise lemma the arrow of time rests on: a state carrying a positive exponent on
some axis has positive length. -/
theorem stateLength_pos_of_axis (z : PrimeAxisTable) (q : PrimeAxis)
    (hq : 0 < rawValue (z.digits q)) : 0 < stateLength z := by
  classical
  have hmem : q ∈ z.digits.support := by
    refine Finsupp.mem_support_iff.mpr ?_
    intro hzero
    rw [hzero] at hq
    simp [rawValue] at hq
  have hterm : 0 < (rawValue (z.digits q) : ℝ) * Real.log (q : ℕ) :=
    mul_pos (by exact_mod_cast hq) (log_prime_pos q)
  refine lt_of_lt_of_le hterm ?_
  refine Finset.single_le_sum (f := fun p => (rawValue (z.digits p) : ℝ) * Real.log (p : ℕ))
    (fun p _ => ?_) hmem
  exact mul_nonneg (by positivity) (le_of_lt (log_prime_pos p))

end D5.S1.Digit.PrimeAxis.GenerationShadow

/- GID: D5/S1/Ledger/GenerationArrowOfTime
   generality: G
   mirror-B: D5/B/S1/Ledger/GenerationArrowOfTime
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-exponent length is additive and strictly increases under nonzero generation. -/

import Mathlib

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'length_strictly_increases_under_generation' D5 Golden/Frozen/accepted`
     finds only this module's declaration and uses; no upstream declaration matches.
   * `rg -n 'eventLength_pos|cashflow_cost_strict_at_event' D5` found
     `D5/S3/Analytic/PrimeCashflowCost.lean`. Its signed events use absolute-value
     cost, not the natural exponent length, additivity, or integer encoding required here.
   * Searches for `Real.log.*Prime`, `primeRadical`, and Finsupp log sums found
     `DoubleFaceLength.sum_exp_log_eq_log` and `PrimeLogIndependence.prime_log_indep`.
     Neither states the arbitrary natural Finsupp result; the finite sum/product pattern
     from `DoubleFaceLength` is reused below.
   * Pinned Mathlib supplies `Finsupp.sum_add_index'`, `Finsupp.sum_pos`,
     `Real.log_prod`, `Real.log_pow`, `Real.log_pos`, and `Nat.Prime.one_lt`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Ledger.GenerationArrowOfTime

/-- A ledger state is a finite-support vector of natural exponents indexed by primes. -/
abbrev PrimeExponent := Nat.Primes →₀ ℕ

/-- The logarithmic length of a prime-exponent ledger state. -/
noncomputable def length (a : PrimeExponent) : ℝ :=
  a.sum fun p exponent => (exponent : ℝ) * Real.log p.1

/-- The natural number encoded by a finite prime-exponent vector. -/
def generatedNumber (a : PrimeExponent) : ℕ :=
  a.prod fun p exponent => p.1 ^ exponent

/-- Logarithmic length is additive under ledger generation. -/
theorem length_add (a u : PrimeExponent) : length (a + u) = length a + length u := by
  classical
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ x y => by push_cast; ring)

/-- Logarithmic length is the logarithm of the encoded natural number. -/
theorem length_eq_log_generatedNumber (a : PrimeExponent) :
    length a = Real.log (generatedNumber a) := by
  classical
  rw [length, generatedNumber, Finsupp.sum, Finsupp.prod]
  push_cast
  rw [Real.log_prod]
  · exact Finset.sum_congr rfl (fun p _ => by rw [Real.log_pow])
  · intro p _
    exact pow_ne_zero _ (by exact_mod_cast p.property.ne_zero)

/-- A nonzero natural prime-exponent vector has strictly positive logarithmic length. -/
theorem length_pos {u : PrimeExponent} (hu : u ≠ 0) : 0 < length u := by
  classical
  rw [length]
  apply Finsupp.sum_pos
  · intro p hp
    have hexponent : 0 < u p :=
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hlog : 0 < Real.log p.1 :=
      Real.log_pos (by exact_mod_cast p.property.one_lt)
    exact mul_pos (by exact_mod_cast hexponent) hlog
  · exact hu

/-- Every nonzero natural prime-exponent update strictly increases logarithmic length. -/
theorem length_strictly_increases_under_generation (a u : PrimeExponent) :
    u ≠ 0 → length (a + u) > length a := by
  intro hu
  rw [length_add]
  exact lt_add_of_pos_right _ (length_pos hu)

example :
    length ((0 : PrimeExponent) + Finsupp.single ⟨2, Nat.prime_two⟩ 1) >
      length (0 : PrimeExponent) := by
  apply length_strictly_increases_under_generation
  exact Finsupp.single_ne_zero.mpr one_ne_zero

#print axioms length_strictly_increases_under_generation

end D5.S1.Ledger.GenerationArrowOfTime

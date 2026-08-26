/- GID: D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime evidence stays positive and is summable exactly above exponent one. -/
/- Library-search audit trail (2026-08-25): repository search found no existing
   `primeEvidence` definition. `ZetaGibbs.summable_real_weight` supplies the
   natural-index convergence theorem and is restricted injectively to primes.
   Pinned mathlib supplies `Nat.Primes.not_summable_one_div` at the boundary and
   `Nat.Primes.summable_rpow` for the exact threshold; both are reused directly. -/

import Mathlib.NumberTheory.SumPrimeReciprocals
import D5.S3.Analytic.ZetaGibbs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold

open D5.S3.Analytic.ZetaGibbs

noncomputable section

/-- The evidence supplied by a prime at exponent `s`. -/
def primeEvidence (s : ℝ) (p : Nat.Primes) : ℝ :=
  (p.1 : ℝ) ^ (-s)

/-- Every prime supplies strictly positive evidence, for every real exponent. -/
theorem primeEvidence_pos (s : ℝ) (p : Nat.Primes) :
    0 < primeEvidence s p := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _

#print axioms primeEvidence_pos

/-- Prime evidence is summable above exponent one. -/
theorem primeEvidence_summable (s : ℝ) (hs : 1 < s) :
    Summable (primeEvidence s) := by
  exact (summable_real_weight s hs).comp_injective Subtype.coe_injective

#print axioms primeEvidence_summable

/-- In particular, the inverse-square prime evidence is summable. -/
theorem primeEvidence_two_summable :
    Summable (primeEvidence 2) := by
  exact primeEvidence_summable 2 (by norm_num)

#print axioms primeEvidence_two_summable

/-- At exponent one, prime evidence is the divergent prime reciprocal series. -/
theorem primeEvidence_one_not_summable :
    ¬ Summable (primeEvidence 1) := by
  change ¬ Summable (fun p : Nat.Primes => (p.1 : ℝ) ^ (-1 : ℝ))
  intro hsum
  exact Nat.Primes.not_summable_one_div (by
    simpa only [Real.rpow_neg_one, one_div] using hsum)

#print axioms primeEvidence_one_not_summable

/-- Exponent one is the exact summability threshold for the prime evidence family. -/
theorem primeEvidence_summable_iff_one_lt (s : ℝ) :
    Summable (primeEvidence s) ↔ 1 < s := by
  change Summable (fun p : Nat.Primes => (p.1 : ℝ) ^ (-s)) ↔ 1 < s
  simpa only [neg_lt_neg_iff] using (Nat.Primes.summable_rpow (r := -s))

#print axioms primeEvidence_summable_iff_one_lt

/-- At and below the threshold, every term is positive but the family is not summable. -/
theorem primeEvidence_at_most_one (s : ℝ) (hs : s ≤ 1) :
    (∀ p : Nat.Primes, 0 < primeEvidence s p) ∧
      ¬ Summable (primeEvidence s) := by
  refine ⟨primeEvidence_pos s, ?_⟩
  rw [primeEvidence_summable_iff_one_lt]
  exact not_lt.mpr hs

#print axioms primeEvidence_at_most_one

/-- At exponent zero, prime evidence is constantly one and is not summable. -/
theorem primeEvidence_zero :
    (∀ p : Nat.Primes, primeEvidence 0 p = 1) ∧
      ¬ Summable (primeEvidence 0) := by
  refine ⟨fun p => ?_, (primeEvidence_at_most_one 0 (by norm_num)).2⟩
  simp [primeEvidence]

#print axioms primeEvidence_zero

/-- At the smallest prime, inverse-square evidence is exactly one quarter. -/
theorem primeEvidence_two_at_two :
    primeEvidence 2 (⟨2, Nat.prime_two⟩ : Nat.Primes) = (1 / 4 : ℝ) := by
  norm_num [primeEvidence, Real.rpow_neg_ofNat]

#print axioms primeEvidence_two_at_two

/-- A positive exponent alone is insufficient for summability: exponent one is a witness. -/
theorem positive_exponent_is_insufficient :
    ∃ s : ℝ, 0 < s ∧ (∀ p : Nat.Primes, 0 < primeEvidence s p) ∧
      ¬ Summable (primeEvidence s) := by
  exact ⟨1, by norm_num, primeEvidence_pos 1, primeEvidence_one_not_summable⟩

#print axioms positive_exponent_is_insufficient

/-- The same prime-indexed family realizes positive summable and positive divergent evidence. -/
theorem primeEvidence_sharp_threshold :
    (∀ p : Nat.Primes, 0 < primeEvidence 2 p) ∧
      Summable (primeEvidence 2) ∧
      (∀ p : Nat.Primes, 0 < primeEvidence 1 p) ∧
      ¬ Summable (primeEvidence 1) := by
  exact ⟨primeEvidence_pos 2, primeEvidence_two_summable,
    primeEvidence_pos 1, primeEvidence_one_not_summable⟩

#print axioms primeEvidence_sharp_threshold

end

end D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold

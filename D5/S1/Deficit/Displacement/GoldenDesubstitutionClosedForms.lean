/- GID: D5/S1/Deficit/Displacement/GoldenDesubstitutionClosedForms
   generality: I
   mirror-B: D5/B/S1/Deficit/Displacement/GoldenDesubstitutionClosedForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proves the individual expansion- and contraction-face closed forms lambdaPlus n = log (nS n) - goldenConj * log n and lambdaMinus n = log (nS n) - goldenRatio * log n for nonzero n by identifying each beta reading with the substituted exponent displacement and assembling the prime-factor logarithm sums. -/

import D5.S1.Deficit.Displacement.GoldenDesubstitutionConjugateLength
import D5.S1.Scale.Fibonacci

open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Deficit
open D5.S1.Deficit.AlmostAdditivity
open D5.S1.Deficit.DoubleFaceLength
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Digit
open D5.S1.Scale
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionLength
open GoldenDesubstitutionZeckendorf

namespace GoldenDesubstitutionClosedForms

local instance : IsTrans ℕ (fun a b => b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem betaDigits_add (r s : RawDigits) :
    betaDigits (r + s) = betaDigits r + betaDigits s := by
  classical
  refine Finsupp.sum_add_index' (fun i => ?_) (fun i m₁ m₂ => ?_)
  · simp
  · push_cast
    ring

@[simp] private theorem betaDigits_single (i : ℕ) :
    betaDigits (Finsupp.single i 1) = phi ^ (i + 2) := by
  classical
  simp [betaDigits]

private theorem betaDigits_rawOfZeckendorf_a {digits : List ℕ}
    (hmin : ∀ k ∈ digits, 2 ≤ k) :
    (betaDigits (rawOfZeckendorf digits)).a =
      ((digits.map fun k => Nat.fib (k + 1)).sum : ℤ) -
        ((digits.map Nat.fib).sum : ℤ) := by
  induction digits with
  | nil => simp [rawOfZeckendorf, betaDigits]
  | cons k digits ih =>
      have hk : 2 ≤ k := hmin k (by simp)
      have htail : ∀ j ∈ digits, 2 ≤ j := by
        intro j hj
        exact hmin j (by simp [hj])
      have hraw : rawOfZeckendorf (k :: digits) =
          Finsupp.single (k - 2) 1 + rawOfZeckendorf digits := by
        rw [rawOfZeckendorf, List.map_cons]
        change Multiset.toFinsupp ({k - 2} + (digits.map fun j => j - 2 : Multiset ℕ)) = _
        rw [Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
        rfl
      rw [hraw, betaDigits_add, a_add, betaDigits_single, ih htail]
      rw [show k - 2 + 2 = k by omega]
      rw [show k = (k - 1) + 1 by omega, golden_phi_pow_a_eq_fib]
      simp only [List.map_cons, List.sum_cons]
      have hk1 : k - 1 + 1 = k := by omega
      have hk2 : k - 1 + 2 = k + 1 := by omega
      simp only [hk1]
      rw [show Nat.fib (k + 1) = Nat.fib (k - 1) + Nat.fib k by
        simpa only [hk1, hk2] using Nat.fib_add_two (n := k - 1)]
      push_cast
      ring

private theorem canonical_two_le {digits : List ℕ} (h : digits.IsZeckendorfRep) :
    ∀ k ∈ digits, 2 ≤ k := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at h
  intro k hk
  exact (List.pairwise_append.mp h).2.2 k hk 0 (by simp)

private theorem betaGolden_a (v : ℕ) :
    (betaGolden v).a = (displacementDecode v : ℤ) - v := by
  rw [betaGolden, toRaw, Z, wEncoding]
  change (betaDigits (rawOfZeckendorf (wdigits v))).a = _
  rw [betaDigits_rawOfZeckendorf_a]
  · simp [displacementDecode, decode_wdigits]
  · intro k hk
    exact canonical_two_le (wdigits_isCanonical v) k hk

private theorem betaReal_eq_displacement (v : ℕ) :
    betaReal v = (displacementDecode v : ℝ) - (v : ℝ) * Real.goldenConj := by
  rw [betaReal, embedding_apply, betaGolden_a, betaGolden_b]
  push_cast
  rw [show Real.goldenRatio = 1 - Real.goldenConj by
    linarith [Real.goldenRatio_add_goldenConj]]
  ring

private theorem betaContraction_eq_displacement (v : ℕ) :
    betaContraction v = (displacementDecode v : ℝ) - (v : ℝ) * Real.goldenRatio := by
  have hspread := betaReal_sub_betaContraction v
  rw [betaReal_eq_displacement, ← Real.goldenRatio_sub_goldenConj] at hspread
  linear_combination -hspread

private theorem log_nS_eq_sum (n : ℕ) :
    Real.log (nS n) =
      n.factorization.sum fun p exponent =>
        (goldenSubstStart exponent : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, nS_factorization]
  rw [Finsupp.sum_mapRange_index (f := goldenSubstStart) (hf := goldenSubstStart_zero)]
  intro p
  simp

/-- The expansion-face length is the hidden-product logarithm minus the golden-conjugate
multiple of the original logarithm. -/
theorem lambdaPlus_eq_log_nS_sub_goldenConj_log (n : ℕ) (hn : n ≠ 0) :
    lambdaPlus n = Real.log (nS n) - Real.goldenConj * Real.log n := by
  by_cases hzero : n = 0
  · exact (hn hzero).elim
  rw [lambdaPlus, log_nS_eq_sum, Real.log_nat_eq_sum_factorization]
  rw [Finsupp.mul_sum, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun p exponent => by
    rw [betaReal_eq_displacement, ← golden_subst_start_eq_displacement_decode]
    ring

/-- The contraction-face length is the hidden-product logarithm minus the golden-ratio
multiple of the original logarithm. -/
theorem lambdaMinus_eq_log_nS_sub_goldenRatio_log (n : ℕ) (hn : n ≠ 0) :
    lambdaMinus n = Real.log (nS n) - Real.goldenRatio * Real.log n := by
  by_cases hzero : n = 0
  · exact (hn hzero).elim
  rw [lambdaMinus, log_nS_eq_sum, Real.log_nat_eq_sum_factorization]
  rw [Finsupp.mul_sum, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun p exponent => by
    rw [betaContraction_eq_displacement, ← golden_subst_start_eq_displacement_decode]
    ring

example : lambdaPlus 1 = Real.log (nS 1) - Real.goldenConj * Real.log 1 := by
  simpa using lambdaPlus_eq_log_nS_sub_goldenConj_log 1 one_ne_zero

end GoldenDesubstitutionClosedForms

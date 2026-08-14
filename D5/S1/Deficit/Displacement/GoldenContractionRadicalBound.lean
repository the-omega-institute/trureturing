/- GID: D5/S1/Deficit/Displacement/GoldenContractionRadicalBound
   generality: I
   mirror-B: D5/B/S1/Deficit/Displacement/GoldenContractionRadicalBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bounds the contraction-face logarithmic error by golden constants times the logarithm of the prime radical, yielding the documented absolute lambdaMinus bound. -/

import D5.S1.Deficit.Displacement.GoldenDesubstitutionClosedForms

open D5.S1.Deficit.AlmostAdditivity
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionClosedForms
open GoldenDesubstitutionLength
open GoldenDesubstitutionZeckendorf

namespace GoldenContractionRadicalBound

private theorem inv_golden_sq_add_inv_golden :
    Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

private theorem golden_subst_start_error_window (v : ℕ) :
    -(Real.goldenRatio⁻¹ ^ 2) ≤
        (goldenSubstStart v : ℝ) - Real.goldenRatio * (v : ℝ) ∧
      (goldenSubstStart v : ℝ) - Real.goldenRatio * (v : ℝ) ≤
        Real.goldenRatio⁻¹ := by
  have hbeattyInt : (goldenSubstStart v : ℤ) =
      ⌊((v : ℝ) + 1) * Real.goldenRatio⌋ - 1 := by
    rw [golden_subst_start_eq_displacement_decode]
    exact displacement_decode_eq_beatty_floor v
  have hbeattyReal := congrArg (fun z : ℤ ↦ (z : ℝ)) hbeattyInt
  push_cast at hbeattyReal
  have hfloorLe :
      ((⌊((v : ℝ) + 1) * Real.goldenRatio⌋ : ℤ) : ℝ) ≤
        ((v : ℝ) + 1) * Real.goldenRatio :=
    Int.floor_le _
  have hfloorLt :
      ((v : ℝ) + 1) * Real.goldenRatio <
        ((⌊((v : ℝ) + 1) * Real.goldenRatio⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hinvsq :
      Real.goldenRatio⁻¹ - 1 = -(Real.goldenRatio⁻¹ ^ 2) := by
    linarith [inv_golden_sq_add_inv_golden]
  have hphi : Real.goldenRatio = 1 + Real.goldenRatio⁻¹ := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  constructor
  · rw [hbeattyReal]
    linarith
  · rw [hbeattyReal]
    linarith

private theorem log_nS_eq_sum (n : ℕ) :
    Real.log (nS n) =
      n.factorization.sum fun p exponent ↦
        (goldenSubstStart exponent : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, nS_factorization]
  rw [Finsupp.sum_mapRange_index (f := goldenSubstStart) (hf := goldenSubstStart_zero)]
  intro p
  simp

private theorem log_primeRadical_eq_sum (n : ℕ) :
    Real.log (primeRadical n) =
      n.factorization.sum fun p _ ↦ Real.log p := by
  rw [primeRadical]
  push_cast
  rw [Real.log_prod]
  · rw [Finsupp.sum, Nat.support_factorization]
  · intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

private theorem log_nS_error_eq_sum (n : ℕ) :
    Real.log (nS n) - Real.goldenRatio * Real.log n =
      n.factorization.sum fun p exponent ↦
        ((goldenSubstStart exponent : ℝ) - Real.goldenRatio * (exponent : ℝ)) *
          Real.log p := by
  rw [log_nS_eq_sum, Real.log_nat_eq_sum_factorization]
  rw [Finsupp.mul_sum, ← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun p exponent ↦ by ring

/-- The hidden-product logarithmic error lies in the sharp interval obtained by summing the
Beatty-floor error on each prime exponent. -/
theorem log_nS_error_radical_window (n : ℕ) :
    -(Real.goldenRatio⁻¹ ^ 2) * Real.log (primeRadical n) ≤
        Real.log (nS n) - Real.goldenRatio * Real.log n ∧
      Real.log (nS n) - Real.goldenRatio * Real.log n ≤
        Real.goldenRatio⁻¹ * Real.log (primeRadical n) := by
  rw [log_nS_error_eq_sum, log_primeRadical_eq_sum]
  constructor
  · rw [Finsupp.mul_sum]
    apply Finsupp.sum_le_sum
    intro p hp
    have hpPrime : Nat.Prime p := by
      apply Nat.prime_of_mem_primeFactors
      simpa only [Nat.support_factorization] using hp
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
    exact mul_le_mul_of_nonneg_right (golden_subst_start_error_window _).1 hlog
  · rw [Finsupp.mul_sum]
    apply Finsupp.sum_le_sum
    intro p hp
    have hpPrime : Nat.Prime p := by
      apply Nat.prime_of_mem_primeFactors
      simpa only [Nat.support_factorization] using hp
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
    exact mul_le_mul_of_nonneg_right (golden_subst_start_error_window _).2 hlog

private theorem log_primeRadical_nonneg (n : ℕ) :
    0 ≤ Real.log (primeRadical n) := by
  rw [log_primeRadical_eq_sum]
  apply Finsupp.sum_nonneg
  intro p hp
  have hpPrime : Nat.Prime p := by
    apply Nat.prime_of_mem_primeFactors
    simpa only [Nat.support_factorization] using hp
  change 0 ≤ Real.log (p : ℝ)
  exact Real.log_nonneg (by exact_mod_cast hpPrime.one_le)

/-- The contraction-face length is bounded by `φ⁻¹` times the logarithm of the prime radical. -/
theorem abs_lambdaMinus_le_goldenRatio_inv_log_primeRadical {n : ℕ} (hn : n ≠ 0) :
    |lambdaMinus n| ≤ Real.goldenRatio⁻¹ * Real.log (primeRadical n) := by
  have hwindow := log_nS_error_radical_window n
  have hlog := log_primeRadical_nonneg n
  have hinvNonneg : 0 ≤ Real.goldenRatio⁻¹ :=
    (inv_pos.mpr Real.goldenRatio_pos).le
  have hinvLeOne : Real.goldenRatio⁻¹ ≤ 1 :=
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio).le
  have hinvSqLe : Real.goldenRatio⁻¹ ^ 2 ≤ Real.goldenRatio⁻¹ := by
    simpa [pow_two] using mul_le_of_le_one_left hinvNonneg hinvLeOne
  rw [lambdaMinus_eq_log_nS_sub_goldenRatio_log n hn]
  apply abs_le.mpr
  refine ⟨?_, hwindow.2⟩
  have hscaled := mul_le_mul_of_nonneg_right hinvSqLe hlog
  linarith [hwindow.1]

example : |lambdaMinus 1| ≤
    Real.goldenRatio⁻¹ * Real.log (primeRadical 1) := by
  exact abs_lambdaMinus_le_goldenRatio_inv_log_primeRadical one_ne_zero

end GoldenContractionRadicalBound

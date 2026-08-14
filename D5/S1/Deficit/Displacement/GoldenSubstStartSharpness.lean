/- GID: D5/S1/Deficit/Displacement/GoldenSubstStartSharpness
   generality: I
   mirror-B: D5/B/S1/Deficit/Displacement/GoldenSubstStartSharpness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Gives the exact golden substitution-start error and proves that both endpoints of its golden window are sharp. -/

import D5.S1.Deficit.Displacement.GoldenContractionRadicalBound

open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionZeckendorf

namespace GoldenSubstStartSharpness

private theorem inv_golden_sq_add_inv_golden :
    Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio]
  nlinarith [Real.goldenConj_sq]

/-- The substitution-start error is the upper endpoint minus one golden fractional part. -/
theorem golden_subst_start_error_eq (v : ℕ) :
    (goldenSubstStart v : ℝ) - Real.goldenRatio * (v : ℝ) =
      Real.goldenRatio⁻¹ -
        Int.fract (((v + 1 : ℕ) : ℝ) * Real.goldenRatio) := by
  have hbeattyInt : (goldenSubstStart v : ℤ) =
      ⌊((v : ℝ) + 1) * Real.goldenRatio⌋ - 1 := by
    rw [golden_subst_start_eq_displacement_decode]
    exact displacement_decode_eq_beatty_floor v
  have hbeattyReal := congrArg (fun z : ℤ ↦ (z : ℝ)) hbeattyInt
  push_cast at hbeattyReal
  have hfract := Int.floor_add_fract (((v : ℝ) + 1) * Real.goldenRatio)
  have hphi : Real.goldenRatio - 1 = Real.goldenRatio⁻¹ := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hbeattyReal]
  linarith

/-- Every substitution-start error lies in the closed golden window. -/
theorem golden_subst_start_error_window (v : ℕ) :
    -(Real.goldenRatio⁻¹ ^ 2) ≤
        (goldenSubstStart v : ℝ) - Real.goldenRatio * (v : ℝ) ∧
      (goldenSubstStart v : ℝ) - Real.goldenRatio * (v : ℝ) ≤
        Real.goldenRatio⁻¹ := by
  rw [golden_subst_start_error_eq]
  constructor
  · have hfract := Int.fract_lt_one
        (((v + 1 : ℕ) : ℝ) * Real.goldenRatio)
    linarith [inv_golden_sq_add_inv_golden]
  · linarith [Int.fract_nonneg
        (((v + 1 : ℕ) : ℝ) * Real.goldenRatio)]

/-- At an odd Fibonacci index, the golden fractional part is the negative conjugate power. -/
theorem fract_fib_mul_goldenRatio (k : ℕ) (hk : Odd k) :
    Int.fract ((Nat.fib k : ℝ) * Real.goldenRatio) =
      -(Real.goldenConj ^ k) := by
  have hneg : Real.goldenConj ^ k < 0 := hk.pow_neg Real.goldenConj_neg
  have hgtNegOne : -(1 : ℝ) < Real.goldenConj ^ k := by
    have hpow := (hk.pow_lt_pow (R := ℝ)).2 Real.neg_one_lt_goldenConj
    rw [hk.neg_one_pow] at hpow
    exact hpow
  have hdecomp :
      (Nat.fib k : ℝ) * Real.goldenRatio =
        (Nat.fib (k + 1) : ℝ) + -(Real.goldenConj ^ k) := by
    nlinarith [Real.fib_succ_sub_goldenRatio_mul_fib k]
  rw [hdecomp, Int.fract_natCast_add]
  exact Int.fract_eq_self.2 ⟨by linarith, by linarith⟩

/-- At an even Fibonacci index, the golden fractional part is one minus the conjugate power. -/
theorem fract_fib_mul_goldenRatio_of_even (k : ℕ) (hk : Even k) :
    Int.fract ((Nat.fib k : ℝ) * Real.goldenRatio) =
      1 - Real.goldenConj ^ k := by
  have hpowEq : Real.goldenConj ^ k = (-Real.goldenConj) ^ k := by
    simpa using hk.neg_pow (-Real.goldenConj)
  have hpowPos : 0 < Real.goldenConj ^ k := hk.pow_pos Real.goldenConj_ne_zero
  have hpowLeOne : Real.goldenConj ^ k ≤ 1 := by
    rw [hpowEq]
    exact pow_le_one₀ (by linarith [Real.goldenConj_neg])
      (by linarith [Real.neg_one_lt_goldenConj])
  have hdecomp :
      (Nat.fib k : ℝ) * Real.goldenRatio =
        (((Nat.fib (k + 1) : ℤ) - 1 : ℤ) : ℝ) +
          (1 - Real.goldenConj ^ k) := by
    push_cast
    nlinarith [Real.fib_succ_sub_goldenRatio_mul_fib k]
  rw [hdecomp, Int.fract_intCast_add]
  exact Int.fract_eq_self.2 ⟨by linarith, by linarith⟩

/-- Errors along odd-index Fibonacci witnesses approach the upper endpoint. -/
theorem golden_subst_start_error_upper_sharp (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ v : ℕ,
      Real.goldenRatio⁻¹ - epsilon <
        (goldenSubstStart v : ℝ) - Real.goldenRatio * (v : ℝ) := by
  have hqPos : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have hqLtOne : Real.goldenRatio⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hepsilon hqLtOne
  let k := 2 * n + 1
  have hk : Odd k := ⟨n, by simp [k, two_mul]⟩
  have hnk : n < k := by omega
  have hpow : Real.goldenRatio⁻¹ ^ k < epsilon :=
    (pow_lt_pow_right_of_lt_one₀ hqPos hqLtOne hnk).trans hn
  have hconjPow : -(Real.goldenConj ^ k) < epsilon := by
    rw [← hk.neg_pow Real.goldenConj, ← Real.inv_goldenRatio]
    exact hpow
  have hfibPos : 0 < Nat.fib k := Nat.fib_pos.2 hk.pos
  refine ⟨Nat.fib k - 1, ?_⟩
  rw [golden_subst_start_error_eq]
  have hindex : Nat.fib k - 1 + 1 = Nat.fib k :=
    Nat.sub_add_cancel hfibPos
  rw [hindex, fract_fib_mul_goldenRatio k hk]
  linarith

/-- Errors along positive even-index Fibonacci witnesses approach the lower endpoint. -/
theorem golden_subst_start_error_lower_sharp (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ v : ℕ,
      (goldenSubstStart v : ℝ) - Real.goldenRatio * (v : ℝ) <
        -(Real.goldenRatio⁻¹ ^ 2) + epsilon := by
  have hqPos : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos
  have hqLtOne : Real.goldenRatio⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hepsilon hqLtOne
  let k := 2 * n + 2
  have hk : Even k := ⟨n + 1, by simp [k, two_mul]; omega⟩
  have hkPos : 0 < k := by omega
  have hnk : n < k := by omega
  have hpow : Real.goldenRatio⁻¹ ^ k < epsilon :=
    (pow_lt_pow_right_of_lt_one₀ hqPos hqLtOne hnk).trans hn
  have hconjPow : Real.goldenConj ^ k < epsilon := by
    calc
      Real.goldenConj ^ k = (-Real.goldenConj) ^ k := by
        simpa using hk.neg_pow (-Real.goldenConj)
      _ = Real.goldenRatio⁻¹ ^ k := by rw [Real.inv_goldenRatio]
      _ < epsilon := hpow
  have hfibPos : 0 < Nat.fib k := Nat.fib_pos.2 hkPos
  refine ⟨Nat.fib k - 1, ?_⟩
  rw [golden_subst_start_error_eq]
  have hindex : Nat.fib k - 1 + 1 = Nat.fib k :=
    Nat.sub_add_cancel hfibPos
  rw [hindex, fract_fib_mul_goldenRatio_of_even k hk]
  linarith [inv_golden_sq_add_inv_golden]

example :
    ∃ v : ℕ,
      (goldenSubstStart v : ℝ) - Real.goldenRatio * (v : ℝ) <
        -(Real.goldenRatio⁻¹ ^ 2) + (1 / 100 : ℝ) := by
  exact golden_subst_start_error_lower_sharp (1 / 100) (by norm_num)

end GoldenSubstStartSharpness

/- GID: D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics
   generality: G
   mirror-B: D5/B/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics
   mirror-E: none(waiver:source-transfer-proof)
   anchors: []
   utility: none
   digest: Licensed original QFT circuit proof support. -/

/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0; the full license is in
Library/Fourier/qudeleap2026qft.md.
Modified for receiver module paths and the retained QFT proof slice.
Source: QudeLeap/Lean-QuantumAlg@971dc8be8a153a116b6d7cd748f984d545861b00.
Original file: QuantumAlg/Primitives/QFT/Mathematics.lean.
Authors: QudeLeap Team
-/

module

public import D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Core.Base.Gate.Unitary
import all D5.S3.Quantum.FourierCircuit.Components.Kets
import all D5.S3.Quantum.FourierCircuit.Util.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace QuantumAlg
open NormalizedVector
noncomputable section

/-! ### Root of unity -/

/-- Primitive `2^n`-th root of unity: `ω_n = e^{2πi/2^n}`
[dW19, qcnotes.tex:1690].
Forward-transform sign convention (`+2πi`, not `−2πi`). -/
@[expose] public def ω (n : ℕ) : ℂ :=
  Complex.exp (↑(2 * Real.pi / (2 : ℝ) ^ n) * Complex.I)
-- [dW19, qcnotes.tex:1690]: ω_N = e^{2πi/N}

/-- `ω_n ^ (2^n) = 1`: `2^n` is a period of the Fourier root. -/
lemma omega_pow_eq_one (n : ℕ) : ω n ^ (2 ^ n) = 1 := by
  rw [ω, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨1, ?_⟩
  push_cast
  have h : (2 : ℝ) ^ n ≠ 0 := ne_of_gt (pow_pos two_pos n)
  field_simp

/-! ### Normalization -/

/-- QFT normalization factor: `1/√(2^n)`, generalizing `NormalizedVector.invSqrt2`. -/
@[expose] public def invSqrtN (n : ℕ) : ℂ := (↑(Real.sqrt ((2 : ℝ) ^ n)))⁻¹

/-- Recursive normalization of the Fourier transform. -/
lemma invSqrtN_succ (n : Nat) :
    invSqrtN (n + 1) = invSqrt2 * invSqrtN n := by
  rw [invSqrtN, invSqrtN, invSqrt2, pow_succ,
    Real.sqrt_mul (by positivity : 0 ≤ (2 : Real) ^ n)]
  push_cast
  rw [mul_inv_rev]

/-- The root for an `n`-qubit transform is the square of the root for the
next larger transform. -/
lemma omega_succ_sq (n : Nat) : ω (n + 1) ^ 2 = ω n := by
  rw [ω, ω, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

/-- The halfway power of the `(n+1)`-qubit Fourier root is minus one. -/
lemma omega_succ_pow_half (n : Nat) :
    ω (n + 1) ^ (2 ^ n) = -1 := by
  rw [ω, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  push_cast
  rw [pow_succ]
  field_simp

@[simp]
lemma omega_succ_pow_period_mul (n multiplier : Nat) :
    ω (n + 1) ^ (2 ^ (n + 1) * multiplier) = 1 := by
  rw [pow_mul, omega_pow_eq_one, one_pow]

/-- Algebraic recurrence of the Fourier phase under the leading-bit/tail
split. -/
lemma qftOmega_pair_recurrence (n reversedTail inputTail : Nat)
    (outputHead inputHead : Fin 2) :
    ω n ^ (reversedTail * inputTail) *
        (if outputHead = 1 then ω (n + 1) ^ inputTail else 1) *
        (if outputHead = 1 ∧ inputHead = 1 then -1 else 1) =
      ω (n + 1) ^
        ((2 * reversedTail + outputHead.val) *
          (inputTail + 2 ^ n * inputHead.val)) := by
  fin_cases outputHead <;> fin_cases inputHead
  · simp only [Fin.ext_iff, Fin.val_one, zero_ne_one, false_and, if_false,
      add_zero, mul_one]
    rw [← omega_succ_sq, ← pow_mul]
    congr 1
    ring
  · simp only [Fin.ext_iff, Fin.val_one, zero_ne_one,
      false_and, if_false, mul_one, add_zero]
    rw [← omega_succ_sq, ← pow_mul]
    have hexponent :
        (2 * reversedTail) * (inputTail + 2 ^ n) =
          2 * (reversedTail * inputTail) +
            2 ^ (n + 1) * reversedTail := by
      rw [pow_succ]
      ring
    rw [hexponent, pow_add, omega_succ_pow_period_mul, mul_one]
  · simp only [Fin.ext_iff, Fin.val_one, zero_ne_one, and_false, if_true,
      if_false, mul_one]
    rw [← omega_succ_sq, ← pow_mul, ← pow_add]
    congr 1
    ring
  · simp only [Fin.ext_iff, Fin.val_one, true_and, if_true, mul_one]
    rw [← omega_succ_sq, ← pow_mul, ← omega_succ_pow_half]
    rw [← pow_add, ← pow_add]
    have hexponent :
        (2 * reversedTail + 1) * (inputTail + 2 ^ n) =
          (2 * (reversedTail * inputTail) + inputTail + 2 ^ n) +
            2 ^ (n + 1) * reversedTail := by
      rw [pow_succ]
      ring
    have hperiod :
        ω (n + 1) ^
            (2 * (reversedTail * inputTail) + inputTail + 2 ^ n +
              2 ^ (n + 1) * reversedTail) =
          ω (n + 1) ^
            (2 * (reversedTail * inputTail) + inputTail + 2 ^ n) := by
      rw [show
          2 * (reversedTail * inputTail) + inputTail + 2 ^ n +
              2 ^ (n + 1) * reversedTail =
            (2 * (reversedTail * inputTail) + inputTail + 2 ^ n) +
              2 ^ (n + 1) * reversedTail by ring,
        pow_add, omega_succ_pow_period_mul, mul_one]
    rw [hexponent, hperiod, pow_add]

end
end QuantumAlg

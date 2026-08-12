/- GID: D5/S1/Deficit/DoubleFaceLength
   generality: I
   mirror-B: D5/B/S1/Deficit/DoubleFaceLength
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Defines the expansion-face length lambdaPlus (the φ-companion of dev's contraction-face lambdaMinus, both prime-exponent sums of the golden face readings) and proves the two-face identity λ₊(n) − λ₋(n) = √5 · log n for n ≠ 0. The core is the per-exponent identity betaReal v − betaContraction v = √5 · v (the expansion minus contraction face of the golden integer betaGolden v, whose φ-coordinate is v), lifted through the prime factorization by 2φ − 1 = √5. This is the two-face spread ("double-face length") difference of 定理 6.47's two closed forms λ± = log n_S − {ψ,φ}·log n, which cancels the hidden-face product n_S; the individual closed forms, the bound |λ₋| ≤ (1/φ)·log rad(n), and the displacement surface 𝔇 are not covered. -/

import D5.S1.Deficit.AlmostAdditivity
import Mathlib

open D5.S1.Deficit
open D5.S1.Deficit.AlmostAdditivity
open D5.S1.Digit
open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Scale
open scoped BigOperators

namespace D5.S1.Deficit.DoubleFaceLength

/-- The φ-coordinate of `phi ^ n` is `fib n` (re-proving the dev-private `phi_pow_b`). -/
theorem phi_pow_b' (n : ℕ) :
    (phi ^ n).b = (Nat.fib n : ℤ) ∧ (phi ^ (n + 1)).b = (Nat.fib (n + 1) : ℤ) := by
  induction n with
  | zero => exact ⟨by simp, by simp [phi]⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hc : phi ^ (n + 2) = phi ^ (n + 1) + phi ^ n := by rw [pow_add, phi_sq]; ring
    rw [hc, b_add, ih.2, ih.1, Nat.fib_add_two]; push_cast; ring

theorem phi_pow_b (n : ℕ) : (phi ^ n).b = (Nat.fib n : ℤ) := (phi_pow_b' n).1

/-- The φ-coordinate of `betaDigits r` is `rawValue r` (re-proving the dev-private `betaDigits_b`). -/
theorem betaDigits_b (r : RawDigits) : (betaDigits r).b = (rawValue r : ℤ) := by
  classical
  induction r using Finsupp.induction with
  | zero => simp [betaDigits, rawValue]
  | single_add i coefficient f _ _ ih =>
      have hbeta : betaDigits (Finsupp.single i coefficient + f)
          = betaDigits (Finsupp.single i coefficient) + betaDigits f := by
        refine Finsupp.sum_add_index' (fun i => ?_) (fun i m₁ m₂ => ?_)
        · simp
        · push_cast; ring
      rw [hbeta, b_add]
      rw [show betaDigits (Finsupp.single i coefficient)
            = (coefficient : GoldenInt) * phi ^ (i + 2) by
          rw [betaDigits, Finsupp.sum_single_index (by simp)]]
      rw [ih, rawValue_add, rawValue_single, b_mul, a_natCast, b_natCast, phi_pow_b]
      simp only [wValue]
      push_cast; ring

/-- The φ-coordinate of the golden integer `betaGolden v` is `v`. -/
theorem betaGolden_b (v : ℕ) : (betaGolden v).b = (v : ℤ) := by
  rw [betaGolden, betaDigits_b, rawValue_toRaw_Z]

/-- `2·φ − 1 = √5`. -/
theorem two_goldenRatio_sub_one : 2 * Real.goldenRatio - 1 = Real.sqrt 5 := by
  have h1 := Real.goldenRatio_sub_goldenConj
  have h2 := Real.goldenRatio_add_goldenConj
  linarith

/-- **Per-exponent two-face identity.** The expansion face minus the contraction face of the golden
integer `betaGolden v` is `√5 · v`: `betaReal v − betaContraction v = √5 · v`. -/
theorem betaReal_sub_betaContraction (v : ℕ) :
    betaReal v - betaContraction v = Real.sqrt 5 * (v : ℝ) := by
  have hb : ((betaGolden v).b : ℝ) = (v : ℝ) := by rw [betaGolden_b]; push_cast; ring
  have hgr := two_goldenRatio_sub_one
  rw [betaReal, betaContraction, embedding_apply, embedding_apply, conj_a, conj_b]
  push_cast
  linear_combination ((betaGolden v).b : ℝ) * hgr + Real.sqrt 5 * hb

/-- **Expansion-face length** `lambdaPlus`, the φ-companion of dev's contraction-face `lambdaMinus`:
the prime-exponent sum of the expansion-face readings `betaReal` weighted by `log p`. -/
noncomputable def lambdaPlus (n : ℕ) : ℝ :=
  n.factorization.sum fun p exponent ↦ betaReal exponent * Real.log p

/-- The prime-exponent-weighted log sum recovers `Real.log n`. -/
theorem sum_exp_log_eq_log (n : ℕ) (hn : n ≠ 0) :
    (n.factorization.sum fun p e ↦ (e : ℝ) * Real.log p) = Real.log n := by
  have hprod : (n : ℝ) = ∏ p ∈ n.factorization.support, ((p : ℝ)) ^ (n.factorization p) := by
    have h := Nat.prod_factorization_pow_eq_self hn
    rw [Finsupp.prod] at h
    calc (n : ℝ) = ((∏ p ∈ n.factorization.support, p ^ (n.factorization p) : ℕ) : ℝ) := by
            rw [h]
      _ = ∏ p ∈ n.factorization.support, ((p : ℝ)) ^ (n.factorization p) := by push_cast; rfl
  rw [Finsupp.sum, hprod, Real.log_prod]
  · exact Finset.sum_congr rfl (fun p _ ↦ by rw [Real.log_pow])
  · intro p hp
    have hpp : 0 < p := Nat.pos_of_mem_primeFactors (by simpa using hp)
    positivity

/-- **Two-face length identity (定理 6.47, difference of the two closed forms).** For `n ≠ 0`, the
expansion-face length minus the contraction-face length is `√5 · log n`:
`lambdaPlus n − lambdaMinus n = √5 · log n`.

This is the two-face spread of `定理 6.47`'s closed forms `λ₊(n) = log n_S − ψ·log n` and
`λ₋(n) = log n_S − φ·log n`: subtracting them cancels the hidden-face product `n_S` and leaves
`(φ − ψ)·log n = √5·log n`. The spread constant `√5 = φ − ψ > 0` is positive because the expansion
face `φ` exceeds the contraction face `ψ`, so the difference `√5·log n` is nonnegative, vanishing
exactly at `n = 1` and strictly positive for `n > 1`. The proof lifts the per-exponent identity
`betaReal v − betaContraction v = √5·v` through the prime factorization.

Only the two-face difference identity is recorded (together with the missing companion definition
`lambdaPlus`). The individual closed forms `λ± = log n_S − {ψ,φ}·log n` relating each face to the
hidden-face product `n_S = ∏_p p^{S(v_p)}`, the bound `|λ₋| ≤ (1/φ)·log rad(n)`, and the displacement
surface `𝔇(s,w)` of the source are **not** covered. -/
theorem lambdaPlus_sub_lambdaMinus (n : ℕ) (hn : n ≠ 0) :
    lambdaPlus n - lambdaMinus n = Real.sqrt 5 * Real.log n := by
  rw [lambdaPlus, lambdaMinus, ← Finsupp.sum_sub]
  rw [show (n.factorization.sum fun p e ↦
        betaReal e * Real.log p - betaContraction e * Real.log p)
      = n.factorization.sum fun p e ↦ Real.sqrt 5 * ((e : ℝ) * Real.log p) from
      Finsupp.sum_congr fun p _ ↦ by rw [← sub_mul, betaReal_sub_betaContraction]; ring]
  rw [← Finsupp.mul_sum, sum_exp_log_eq_log n hn]

end D5.S1.Deficit.DoubleFaceLength

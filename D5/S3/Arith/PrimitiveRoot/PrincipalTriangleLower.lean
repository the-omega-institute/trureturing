/- GID: D5/S3/Arith/PrimitiveRoot/PrincipalTriangleLower
   generality: G
   mirror-B: D5/B/S3/Arith/PrimitiveRoot/PrincipalTriangleLower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: Discrete integration of the unconditional Chebyshev lower estimate. -/

import D5.S3.Arith.PrimitiveRoot.ChebyshevThirty
import D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Summing full Mangoldt prefixes retains prime powers in the principal term. -/

namespace D5.S3.Arith.PrimitiveRoot.PrincipalTriangleLower

open scoped BigOperators
open Finset
open D5.S3.Weil.Mertens.IntegratedExplicit.TriangleRampZeta
open ChebyshevThirty

private theorem psi_nat_range (n : ℕ) :
    Chebyshev.psi n = ∑ k ∈ range (n + 1), ArithmeticFunction.vonMangoldt k := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero]

private theorem prefix_sum_identity (p : ℕ) :
    ∑ k ∈ range p, Chebyshev.psi k =
      ∑ n ∈ range p, ArithmeticFunction.vonMangoldt n * ((p : ℝ) - n) := by
  induction p with
  | zero => simp
  | succ p ih =>
    simp only [sum_range_succ]
    rw [ih, psi_nat_range, sum_range_succ]
    simp_rw [Nat.cast_add, Nat.cast_one]
    have hpoint (n : ℕ) : ArithmeticFunction.vonMangoldt n *
        ((p : ℝ) + 1 - n) =
        ArithmeticFunction.vonMangoldt n * ((p : ℝ) - n) +
          ArithmeticFunction.vonMangoldt n := by ring
    simp_rw [hpoint, sum_add_distrib]
    ring

/-- Exact discrete integration of the strict triangular Mangoldt sum. -/
private theorem smoothedMangoldt_eq_prefix_average (p : ℕ) (hp : 0 < p) :
    smoothedMangoldt p = (∑ k ∈ range p, Chebyshev.psi k) / p := by
  rw [prefix_sum_identity, smoothedMangoldt, Nat.ceil_natCast, sum_div]
  apply sum_congr rfl
  intro n hn
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

/-- Summation of Chebyshev's estimate gives a finite explicit triangular lower bound. -/
private theorem smoothedMangoldt_chebyshev (p : ℕ) (hp : 1 ≤ p) :
    coefficient * ((p : ℝ) - 1) / 2 - 5 * (1 + Real.log p) ≤
      smoothedMangoldt p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have hpoint (k : ℕ) (hk : k ∈ range p) :
      coefficient * k - 5 * (1 + Real.log p) ≤ Chebyshev.psi k := by
    rcases eq_or_ne k 0 with rfl | hk0
    · simp only [Nat.cast_zero, mul_zero, zero_sub, Chebyshev.psi_zero]
      linarith
    have h := psi_nat_lower k (by omega)
    have hkp : (k : ℝ) ≤ p := by exact_mod_cast (mem_range.mp hk).le
    have hkl : Real.log k ≤ Real.log p :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk0) hkp
    linarith
  have hsum := sum_le_sum hpoint
  have hid : (∑ k ∈ range p, (k : ℝ)) * 2 = (p : ℝ) * ((p : ℝ) - 1) := by
    have h := sum_range_id_mul_two p
    have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hp)
    have hR := congrArg (fun n : ℕ => (n : ℝ)) h
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, hp1] using hR
  simp only [sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at hsum
  rw [smoothedMangoldt_eq_prefix_average p (by omega)]
  apply (le_div_iff₀ hpR).mpr
  have heq : coefficient * (∑ k ∈ range p, (k : ℝ)) =
      coefficient * (p : ℝ) * ((p : ℝ) - 1) / 2 := by
    calc
      _ = coefficient * ((∑ k ∈ range p, (k : ℝ)) * 2) / 2 := by ring
      _ = _ := by rw [hid]; ring
  rw [heq] at hsum
  nlinarith

private theorem log_large_bound {x : ℝ} (hx : 5000000 ≤ x) :
    Real.log x ≤ x / 50000 := by
  have hbase : Real.log (5000000 : ℝ) < 16 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 5000000)
      (by norm_num : (5000000 : ℝ) < 2 ^ (23 : ℕ))
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    nlinarith [Real.log_two_lt_d9]
  have hx0 : 0 < x := by linarith
  have ht := Real.log_le_sub_one_of_pos (by positivity : 0 < x / 5000000)
  rw [Real.log_div hx0.ne' (by norm_num)] at ht
  linarith

/-- An unconditional principal triangular estimate with epsilon equal to 1/25. -/
private theorem smoothedMangoldt_large (p : ℕ) (hp : 5000000 ≤ p) :
    (23 / 50 : ℝ) * p ≤ smoothedMangoldt p := by
  have hpR : (5000000 : ℝ) ≤ p := by exact_mod_cast hp
  have hs := smoothedMangoldt_chebyshev p (by omega)
  have hc := coefficient_bounds
  have hl := log_large_bound hpR
  have hcpos : 0 ≤ coefficient := by linarith [hc.1]
  have hmul := mul_le_mul_of_nonneg_right hc.1
    (show 0 ≤ (p : ℝ) - 1 by linarith)
  nlinarith

/-- The prime-modulus principal sum retains the full Mangoldt triangular mass. -/
theorem principal_smoothedCharacterSum_large {p : ℕ} (hp : p.Prime)
    (hlarge : 5000000 ≤ p) :
    (23 / 50 : ℝ) * p ≤ (CharacterSieve.smoothedCharacterSum p 1).re := by
  rw [principal_smoothedCharacterSum_eq hp]
  exact smoothedMangoldt_large p hlarge

#print axioms principal_smoothedCharacterSum_large

end D5.S3.Arith.PrimitiveRoot.PrincipalTriangleLower

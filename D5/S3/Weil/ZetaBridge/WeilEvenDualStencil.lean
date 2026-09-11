/- GID: D5/S3/Weil/ZetaBridge/WeilEvenDualStencil
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilEvenDualStencil
   mirror-E: none(waiver:actual-Fourier-domain-and-interval-dual-consumer)
   anchors: []
   utility: none
   digest: Evaluate and bound the actual arithmetic column of a zero-trace even Fourier stencil, with all prime, pole and Gamma terms retained. -/

import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/-!
# Actual even zero-trace columns for arithmetic energy-dual trials

The trial generator is V_n + V_(-n) - 2 V_0. Its endpoint trace vanishes.
The source proves oddness of the existing arithmeticBoundarySymbol from its
actual prime/pole/infinite-Gamma expression, then evaluates the existing
couplingColumn on this stencil. The resulting inverse-square estimate uses
sum n*norm(t_n), rather than a separate hypothesis about zero moments.

The numerical consumer reconstructs two Gaussian-rational pivots to impose
both the endpoint condition and exact pairing with the already-fixed Weil
candidate. It certifies the full dual residual, not only its exterior tail.
The general variational theorem is reused from PR #5882 on paper; it is not
re-proved here. Fourier/operator identification, the full-space spectral
certificate and the executable interval result retain their separate scope.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilEvenDualStencil

open scoped BigOperators
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

-- A private definitional presentation of the existing symbol at a real
-- frequency. It introduces no second public arithmetic or Fourier owner.
private def symbolAt (c : ℕ) (w : ℝ) : ℝ :=
  -(2 * w * (Real.cosh (Real.log (c : ℝ) / 2) - 1) / (w ^ 2 + 1 / 4))
  - (∑' j : ℕ, w * (1 - Real.exp (-(2 * (j : ℝ) + 1 / 2) * Real.log (c : ℝ))) /
      ((2 * (j : ℝ) + 1 / 2) ^ 2 + w ^ 2))
  - ∑ j ∈ Finset.range c,
      (ArithmeticFunction.vonMangoldt j / Real.sqrt j) * Real.sin (w * Real.log j)

private theorem symbolAt_neg (c : ℕ) (w : ℝ) : symbolAt c (-w) = -symbolAt c w := by
  simp only [symbolAt, neg_sq, mul_neg, neg_mul, neg_div,
    Real.sin_neg, tsum_neg, Finset.sum_neg_distrib]
  ring

/-- Reflection of the actual arithmetic symbol, including the complete Gamma
series. This is proved from the original defining expression, not postulated. -/
theorem arithmetic_boundary_symbol_neg (c : ℕ) (n : ℤ) :
    arithmeticBoundarySymbol c (-n) = -arithmeticBoundarySymbol c n := by
  change symbolAt c (2 * Real.pi * ((-n : ℤ) : ℝ) / Real.log (c : ℝ)) =
    -symbolAt c (2 * Real.pi * (n : ℝ) / Real.log (c : ℝ))
  simp only [Int.cast_neg, mul_neg, neg_div, symbolAt_neg]

/-- The central symbol of the existing arithmetic lattice vanishes. -/
theorem arithmetic_boundary_symbol_zero (c : ℕ) : arithmeticBoundarySymbol c 0 = 0 := by
  have h := arithmetic_boundary_symbol_neg c 0
  simp only [neg_zero] at h
  linarith

/-- The existing exterior column for V_n+V_(-n)-2V_0. The support and its
coefficients are given before evaluating the arithmetic action. -/
def zeroTraceColumn (c : ℕ) (n m : ℤ) : ℂ :=
  couplingColumn c {n, -n, 0} (fun j => if j = 0 then -2 else 1) m

private theorem separated_denominators {n m : ℝ} (hn : 0 < n) (hm : n < |m|) :
    m ≠ 0 ∧ m - n ≠ 0 ∧ m + n ≠ 0 ∧ 0 < m ^ 2 - n ^ 2 := by
  have hpos : 0 < (|m| - n) * (|m| + n) :=
    mul_pos (sub_pos.mpr hm) (by linarith [abs_nonneg m])
  have hs : 0 < m ^ 2 - n ^ 2 := by nlinarith [sq_abs m]
  refine ⟨?_, ?_, ?_, hs⟩ <;> intro h <;> nlinarith [sq_nonneg n]

/-- Exact canonical arithmetic stencil column at every separated exterior
integer frequency. Its first-order term cancels; the arithmetic numerator
and both denominator factors are retained, including the sign of m. -/
theorem zero_trace_column_formula (c : ℕ) {n m : ℤ} (hn : 0 < n)
    (hm : (n : ℝ) < |(m : ℝ)|) :
    zeroTraceColumn c n m =
      (((2 * (n : ℝ) * ((m : ℝ) * arithmeticBoundarySymbol c n -
          (n : ℝ) * arithmeticBoundarySymbol c m)) /
        (Real.pi * (m : ℝ) * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
  classical
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hneg0 : -n ≠ 0 := neg_ne_zero.mpr hn0
  have hnneg : n ≠ -n := by intro h; linarith
  have hmem : n ∉ ({-n, 0} : Finset ℤ) := by simp [hnneg, hn0]
  have hnegmem : -n ∉ ({0} : Finset ℤ) := by simp [hneg0]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨hm0, hmn, hmp, hs⟩ := separated_denominators hnR hm
  rw [zeroTraceColumn, couplingColumn, Finset.sum_insert hmem,
    Finset.sum_insert hnegmem, Finset.sum_singleton]
  simp only [if_neg hn0, if_neg hneg0, if_pos rfl, mul_one,
    arithmetic_boundary_symbol_neg, arithmetic_boundary_symbol_zero,
    Int.cast_neg, Int.cast_zero, sub_zero, zero_sub, sub_neg_eq_add]
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
  have h1 : (m : ℂ) - (n : ℂ) ≠ 0 := by exact_mod_cast hmn
  have h2 : (m : ℂ) + (n : ℂ) ≠ 0 := by exact_mod_cast hmp
  have h3 : (m : ℂ) ^ 2 - (n : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hs.ne'
  field_simp [hp, h0, h1, h2, h3]
  <;> ring

/-- The paired zero-trace stencil gains inverse-square decay with an exact
factorization of the elementary envelope. The bound is all-scale and applies
to both signs of m. No matrix cutoff, moment hypothesis or omitted prime term
is used to obtain it. -/
theorem zero_trace_column_bound {c : ℕ} (hc : 2 ≤ c) {n m : ℤ}
    (hn : 0 < n) (hm : 2 * (n : ℝ) ≤ |(m : ℝ)|) :
    ‖zeroTraceColumn c n m‖ ≤
      4 * arithmeticBoundaryBudget c * (n : ℝ) / (Real.pi * |(m : ℝ)| ^ 2) := by
  let B := arithmeticBoundaryBudget c
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsep : (n : ℝ) < |(m : ℝ)| := by linarith
  obtain ⟨hm0, hmn, hmp, hs⟩ := separated_denominators hnR hsep
  have hy : 0 < |(m : ℝ)| := hnR.trans hsep
  have hg : 0 < |(m : ℝ)| - (n : ℝ) := sub_pos.mpr hsep
  have hsn : |arithmeticBoundarySymbol c n| ≤ B := (arithmetic_boundary_symbol_bound hc n).2
  have hsm : |arithmeticBoundarySymbol c m| ≤ B := (arithmetic_boundary_symbol_bound hc m).2
  have hB : 0 ≤ B := (abs_nonneg _).trans hsn
  have hnum : |(m : ℝ) * arithmeticBoundarySymbol c n -
      (n : ℝ) * arithmeticBoundarySymbol c m| ≤ B * (|(m : ℝ)| + (n : ℝ)) := by
    calc
      _ ≤ |(m : ℝ) * arithmeticBoundarySymbol c n| +
          |(n : ℝ) * arithmeticBoundarySymbol c m| := abs_sub _ _
      _ = |(m : ℝ)| * |arithmeticBoundarySymbol c n| +
          (n : ℝ) * |arithmeticBoundarySymbol c m| := by
        rw [abs_mul, abs_mul, abs_of_pos hnR]
      _ ≤ |(m : ℝ)| * B + (n : ℝ) * B :=
        add_le_add (mul_le_mul_of_nonneg_left hsn (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hsm hnR.le)
      _ = _ := by ring
  rw [zero_trace_column_formula c hn hsep, Complex.norm_real, Real.norm_eq_abs]
  simp only [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hnR,
    abs_of_pos hs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (2 * (n : ℝ) * (B * (|(m : ℝ)| + (n : ℝ)))) /
        (Real.pi * |(m : ℝ)| * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by positivity)) (by positivity)
    _ = 2 * B * (n : ℝ) /
        (Real.pi * |(m : ℝ)| * (|(m : ℝ)| - (n : ℝ))) := by
      rw [← sq_abs (m : ℝ)]
      have hh : |(m : ℝ)| + (n : ℝ) ≠ 0 := by positivity
      have hh2 : |(m : ℝ)| ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by rw [sq_abs]; exact hs.ne'
      field_simp [Real.pi_ne_zero, hy.ne', hg.ne', hh, hh2]
      <;> ring
    _ ≤ 2 * B * (n : ℝ) / (Real.pi * |(m : ℝ)| * (|(m : ℝ)| / 2)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by
      change 2 * B * (n : ℝ) / (Real.pi * |(m : ℝ)| * (|(m : ℝ)| / 2)) =
        4 * B * (n : ℝ) / (Real.pi * |(m : ℝ)| ^ 2)
      field_simp [Real.pi_ne_zero, hy.ne']
      <;> ring

/-- Complete finite synthesis of the actual paired columns. The weighted
coefficient mass sum n*norm(t_n) is computed from the explicit trial. This is
the tail constant consumed by the actual full-residual interval certificate. -/
theorem finite_zero_trace_columns_bound {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (t : ℤ → ℂ) (m : ℤ)
    (hpos : ∀ n ∈ S, 0 < n)
    (hsep : ∀ n ∈ S, 2 * (n : ℝ) ≤ |(m : ℝ)|) :
    ‖∑ n ∈ S, t n * zeroTraceColumn c n m‖ ≤
      (4 * arithmeticBoundaryBudget c / (Real.pi * |(m : ℝ)| ^ 2)) *
        ∑ n ∈ S, (n : ℝ) * ‖t n‖ := by
  calc
    _ ≤ ∑ n ∈ S, ‖t n * zeroTraceColumn c n m‖ := norm_sum_le _ _
    _ = ∑ n ∈ S, ‖t n‖ * ‖zeroTraceColumn c n m‖ := by simp only [norm_mul]
    _ ≤ ∑ n ∈ S, ‖t n‖ *
        (4 * arithmeticBoundaryBudget c * (n : ℝ) / (Real.pi * |(m : ℝ)| ^ 2)) :=
      Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
        (zero_trace_column_bound hc (hpos n hn) (hsep n hn)) (norm_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring

#print axioms arithmetic_boundary_symbol_neg
#print axioms arithmetic_boundary_symbol_zero
#print axioms zero_trace_column_formula
#print axioms zero_trace_column_bound
#print axioms finite_zero_trace_columns_bound

end D5.S3.Weil.ZetaBridge.WeilEvenDualStencil

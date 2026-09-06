/- GID: D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet
   mirror-E: none(waiver:analytic-estimate-with-separate-interval-certificate)
   anchors: []
   digest: Bound the actual prime-pole-Gamma boundary symbol and its exterior coupling remainder. -/

import D5.S3.Weil.ZetaCore.ExplicitFormula
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The arithmetic boundary symbol controls the infinite coupling tail

For c>=2, L=log c and omega_n=2*pi*n/L, the boundary symbol retains the pole,
Gamma and finite von Mangoldt terms of the Weil form. Its Gamma series is
proved absolutely convergent, and the bound on the symbol is proved from its
explicit terms. No bound on an unspecified operator is assumed.

In the phase-adjusted orthonormal Fourier basis, the off-diagonal matrix entry
is (s_n-s_m)/(pi*(m-n)). The Fourier/domain identification with the canonical
Weil form follows the calculations of Connes--Consani--Moscovici,
arXiv:2511.22755, Lemma 2.3 and Section 4, and is proved on paper in the existing
RH theory volume. It is not claimed to be a theorem of this Lean file.

The first coupling jet retains the moments sum v_n and sum s_n*v_n. The public
remainder theorem applies at every exterior integer mode, with no upper mode
cutoff. Summing its square, together with the retained moment term, gives the
positive rank-two tail majorant used by the independent interval certificate.
That infinite Gram summation and the c=3 full-form Schur certificate remain
separate paper/computer-assisted results, not Lean conclusions of this file.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

open scoped BigOperators
noncomputable section

private def gammaRate (j : ℕ) : ℝ := 2 * (j : ℝ) + 1 / 2
private def gammaMajorant (w : ℝ) (j : ℕ) : ℝ :=
  w / (gammaRate j ^ 2 + w ^ 2)
private def gammaSineTerm (L w : ℝ) (j : ℕ) : ℝ :=
  w * (1 - Real.exp (-gammaRate j * L)) / (gammaRate j ^ 2 + w ^ 2)
private def logLength (c : ℕ) : ℝ := Real.log (c : ℝ)
private def frequency (c : ℕ) (n : ℤ) : ℝ := 2 * Real.pi * (n : ℝ) / logLength c
private def primeWeight (j : ℕ) : ℝ := ArithmeticFunction.vonMangoldt j / Real.sqrt j
private def poleSine (L w : ℝ) : ℝ :=
  2 * w * (Real.cosh (L / 2) - 1) / (w ^ 2 + 1 / 4)

/-- The actual arithmetic boundary symbol, at the integer Fourier lattice.
The endpoint n=c may be omitted because its sine contribution is zero.
The infinite Gamma series is not totalized to zero: convergence is proved below. -/
def arithmeticBoundarySymbol (c : ℕ) (n : ℤ) : ℝ :=
  -poleSine (logLength c) (frequency c n)
  - (∑' j : ℕ, gammaSineTerm (logLength c) (frequency c n) j)
  - ∑ j ∈ Finset.range c, primeWeight j * Real.sin (frequency c n * Real.log j)

/-- An independently constructed arithmetic envelope. Absolute values of the
finite prime weights avoid needing a separate positivity assumption. -/
def arithmeticBoundaryBudget (c : ℕ) : ℝ :=
  2 * Real.cosh (logLength c / 2) + ∑ j ∈ Finset.range c, |primeWeight j|

private theorem gammaRate_pos (j : ℕ) : 0 < gammaRate j := by
  unfold gammaRate
  positivity

private theorem majorant_nonneg {w : ℝ} (hw : 0 ≤ w) (j : ℕ) :
    0 ≤ gammaMajorant w j := by
  unfold gammaMajorant
  positivity

private theorem majorant_zero_le_one {w : ℝ} (hw : 0 ≤ w) :
    gammaMajorant w 0 ≤ 1 := by
  unfold gammaMajorant gammaRate
  norm_num only [Nat.cast_zero, mul_zero, zero_add]
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg (w - 1 / 2)]

private theorem majorant_step {w : ℝ} (hw : 0 ≤ w) (j : ℕ) :
    gammaMajorant w (j + 1) ≤
      w * ((w + 2 * (j : ℝ) + 1 / 2)⁻¹ -
        (w + 2 * (j : ℝ) + 1 / 2 + 2)⁻¹) := by
  let d : ℝ := w + 2 * (j : ℝ) + 1 / 2
  let D : ℝ := (2 * (j : ℝ) + 5 / 2) ^ 2 + w ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hd2 : 0 < d + 2 := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hden : d * (d + 2) ≤ 2 * D := by
    dsimp [d, D]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith [sq_nonneg (w - 2 * (j : ℝ) - 3 / 2)]
  have hinv : 1 / D ≤ 2 / (d * (d + 2)) := by
    apply (div_le_div_iff₀ hD (mul_pos hd hd2)).mpr
    nlinarith
  calc
    gammaMajorant w (j + 1) = w * (1 / D) := by
      have hb : gammaRate (j + 1) = 2 * (j : ℝ) + 5 / 2 := by
        dsimp [gammaRate]
        push_cast
        ring
      rw [gammaMajorant, hb]
      dsimp [D]
      ring
    _ ≤ w * (2 / (d * (d + 2))) := mul_le_mul_of_nonneg_left hinv hw
    _ = _ := by
      change w * (2 / (d * (d + 2))) = w * (d⁻¹ - (d + 2)⁻¹)
      field_simp [ne_of_gt hd, ne_of_gt hd2]
      <;> ring

private theorem majorant_tail_partial {w : ℝ} (hw : 0 ≤ w) (M : ℕ) :
    (∑ j ∈ Finset.range M, gammaMajorant w (j + 1)) ≤
      w * ((w + 1 / 2)⁻¹ - (w + 1 / 2 + 2 * (M : ℝ))⁻¹) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have hstep := majorant_step hw M
      have heq : w + 2 * (M : ℝ) + 1 / 2 = w + 1 / 2 + 2 * (M : ℝ) := by ring
      rw [heq] at hstep
      have hnext : w + 1 / 2 + 2 * ((M + 1 : ℕ) : ℝ) =
          w + 1 / 2 + 2 * (M : ℝ) + 2 := by push_cast; ring
      rw [hnext]
      simp only [mul_sub] at ih hstep ⊢
      linarith

private theorem majorant_partial_le_two {w : ℝ} (hw : 0 ≤ w) (M : ℕ) :
    (∑ j ∈ Finset.range M, gammaMajorant w j) ≤ 2 := by
  cases M with
  | zero => simp
  | succ M =>
      rw [Finset.sum_range_succ']
      have ht := majorant_tail_partial hw M
      have h0 := majorant_zero_le_one hw
      have hratio : w * (w + 1 / 2)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact (div_le_one (by positivity)).mpr (by linarith)
      have hlast : 0 ≤ w * (w + 1 / 2 + 2 * (M : ℝ))⁻¹ := by positivity
      simp only [mul_sub] at ht
      linarith

private theorem majorant_summable {w : ℝ} (hw : 0 ≤ w) :
    Summable (gammaMajorant w) :=
  summable_of_sum_range_le (majorant_nonneg hw) (majorant_partial_le_two hw)

private theorem majorant_tsum_le_two {w : ℝ} (hw : 0 ≤ w) :
    (∑' j : ℕ, gammaMajorant w j) ≤ 2 :=
  Real.tsum_le_of_sum_range_le (majorant_nonneg hw) (majorant_partial_le_two hw)

private theorem sineTerm_abs_le {L : ℝ} (hL : 0 ≤ L) (w : ℝ) (j : ℕ) :
    |gammaSineTerm L w j| ≤ gammaMajorant |w| j := by
  have hb := gammaRate_pos j
  have he : Real.exp (-gammaRate j * L) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) hL)
  have he0 := Real.exp_pos (-gammaRate j * L)
  have hf : 0 ≤ 1 - Real.exp (-gammaRate j * L) := sub_nonneg.mpr he
  have hf1 : 1 - Real.exp (-gammaRate j * L) ≤ 1 := by linarith
  have hd : 0 < gammaRate j ^ 2 + w ^ 2 := by positivity
  unfold gammaSineTerm gammaMajorant
  rw [abs_div, abs_mul, abs_of_nonneg hf, abs_of_pos hd, sq_abs]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right (abs_nonneg w) hf1) hd.le

private theorem sineTerm_norm_summable {L : ℝ} (hL : 0 ≤ L) (w : ℝ) :
    Summable (fun j => ‖gammaSineTerm L w j‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => ?_) (majorant_summable (abs_nonneg w))
  simpa only [Real.norm_eq_abs] using sineTerm_abs_le hL w j

private theorem gamma_sine_abs_le_two {L : ℝ} (hL : 0 ≤ L) (w : ℝ) :
    |∑' j : ℕ, gammaSineTerm L w j| ≤ 2 := by
  have hs := sineTerm_norm_summable hL w
  calc
    _ = ‖∑' j : ℕ, gammaSineTerm L w j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' j : ℕ, ‖gammaSineTerm L w j‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, gammaMajorant |w| j :=
      hs.tsum_le_tsum (fun j => by simpa only [Real.norm_eq_abs] using sineTerm_abs_le hL w j)
        (majorant_summable (abs_nonneg w))
    _ ≤ 2 := majorant_tsum_le_two (abs_nonneg w)

private theorem pole_abs_le (L w : ℝ) :
    |poleSine L w| ≤ 2 * (Real.cosh (L / 2) - 1) := by
  have hc : 0 ≤ Real.cosh (L / 2) - 1 := sub_nonneg.mpr (Real.one_le_cosh _)
  have hd : 0 < w ^ 2 + (1 / 4 : ℝ) := by positivity
  have hw : |w| ≤ w ^ 2 + 1 / 4 := by
    nlinarith [sq_nonneg (|w| - 1 / 2), sq_abs w]
  unfold poleSine
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg hc, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have h := mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num) hc)
  nlinarith

private theorem prime_abs_le (c : ℕ) (w : ℝ) :
    |∑ j ∈ Finset.range c, primeWeight j * Real.sin (w * Real.log j)| ≤
      ∑ j ∈ Finset.range c, |primeWeight j| := by
  calc
    _ ≤ ∑ j ∈ Finset.range c, |primeWeight j * Real.sin (w * Real.log j)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (Finset.range c) (fun j => primeWeight j * Real.sin (w * Real.log j)))
    _ ≤ _ := Finset.sum_le_sum (fun j _ => by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))

/-- Absolute convergence and a uniform envelope for the concrete arithmetic
boundary symbol. All pole, Gamma and finite prime terms are accounted for.
No zero data, positivity hypothesis, or unknown operator bound is supplied. -/
theorem arithmetic_boundary_symbol_bound {c : ℕ} (hc : 2 ≤ c) (n : ℤ) :
    Summable (fun j => ‖gammaSineTerm (logLength c) (frequency c n) j‖) ∧
    |arithmeticBoundarySymbol c n| ≤ arithmeticBoundaryBudget c := by
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hc)
  have hL : 0 ≤ logLength c := Real.log_nonneg hc1
  refine ⟨sineTerm_norm_summable hL _, ?_⟩
  have hp := pole_abs_le (logLength c) (frequency c n)
  have hg := gamma_sine_abs_le_two hL (frequency c n)
  have hpr := prime_abs_le c (frequency c n)
  have h1 := abs_sub (-poleSine (logLength c) (frequency c n))
    (∑' j : ℕ, gammaSineTerm (logLength c) (frequency c n) j)
  have h2 := abs_sub
    (-poleSine (logLength c) (frequency c n) -
      (∑' j : ℕ, gammaSineTerm (logLength c) (frequency c n) j))
    (∑ j ∈ Finset.range c, primeWeight j * Real.sin (frequency c n * Real.log j))
  rw [abs_neg] at h1
  unfold arithmeticBoundarySymbol arithmeticBoundaryBudget
  linarith

/-- The exterior column of the arithmetic divided-difference matrix. Its
identification with the canonical Weil operator is a separate Fourier bridge. -/
def couplingColumn (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) : ℂ :=
  ∑ n ∈ S, (((arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
    (Real.pi * ((m : ℝ) - (n : ℝ))) : ℝ) : ℂ) * v n

/-- The first exterior jet. Collecting the finite sum gives
`(sum s_n*v_n - s_m*sum v_n)/(pi*m)`, retaining two boundary moments. -/
def couplingFirstJet (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) : ℂ :=
  ∑ n ∈ S, (((arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
    (Real.pi * (m : ℝ)) : ℝ) : ℂ) * v n

private theorem coefficient_remainder {x y sn sm B N : ℝ}
    (hN : 0 ≤ N) (hx : |x| ≤ N) (hy : N < |y|)
    (hsn : |sn| ≤ B) (hsm : |sm| ≤ B) :
    |(sn - sm) / (Real.pi * (y - x)) - (sn - sm) / (Real.pi * y)| ≤
      2 * B * N / (Real.pi * |y| * (|y| - N)) := by
  have hB : 0 ≤ B := (abs_nonneg sn).trans hsn
  have hy0 : 0 < |y| := lt_of_le_of_lt hN hy
  have hgap : 0 < |y| - N := sub_pos.mpr hy
  have htri := abs_add_le (y - x) x
  rw [sub_add_cancel] at htri
  have hrev : |y| - N ≤ |y - x| := by linarith
  have hdiff : 0 < |y - x| := lt_of_lt_of_le hgap hrev
  have hyn : y ≠ 0 := abs_pos.mp hy0
  have hdn : y - x ≠ 0 := abs_pos.mp hdiff
  have hid : (sn - sm) / (Real.pi * (y - x)) - (sn - sm) / (Real.pi * y) =
      (sn - sm) * x / (Real.pi * y * (y - x)) := by
    field_simp [Real.pi_ne_zero, hyn, hdn]
    <;> ring
  have hnum : |sn - sm| * |x| ≤ 2 * B * N := by
    have hs : |sn - sm| ≤ 2 * B := (abs_sub sn sm).trans (by linarith)
    exact mul_le_mul hs hx (abs_nonneg x) (by positivity)
  have hden : Real.pi * |y| * (|y| - N) ≤ Real.pi * |y| * |y - x| :=
    mul_le_mul_of_nonneg_left hrev (by positivity)
  rw [hid, abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  calc
    _ ≤ (2 * B * N) / (Real.pi * |y| * |y - x|) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-- Every exterior integer mode has an explicit first-jet remainder. The bound
uses the actual, independently bounded arithmetic symbol, and works at every
prime cutoff c>=2. N bounds the finite interior indices; |m|>N is the sole
frequency separation assumption. There is no finite exterior upper cutoff. -/
theorem arithmetic_coupling_first_jet_error {c : ℕ} (hc : 2 ≤ c)
    (S : Finset ℤ) (v : ℤ → ℂ) {N : ℝ} (hN : 0 ≤ N)
    (hS : ∀ n ∈ S, |(n : ℝ)| ≤ N) {m : ℤ} (hm : N < |(m : ℝ)|) :
    ‖couplingColumn c S v m - couplingFirstJet c S v m‖ ≤
      (2 * arithmeticBoundaryBudget c * N /
        (Real.pi * |(m : ℝ)| * (|(m : ℝ)| - N))) * ∑ n ∈ S, ‖v n‖ := by
  let a (n : ℤ) : ℝ := (arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
    (Real.pi * ((m : ℝ) - (n : ℝ)))
  let b (n : ℤ) : ℝ := (arithmeticBoundarySymbol c n - arithmeticBoundarySymbol c m) /
    (Real.pi * (m : ℝ))
  let K : ℝ := 2 * arithmeticBoundaryBudget c * N /
    (Real.pi * |(m : ℝ)| * (|(m : ℝ)| - N))
  have hab (n : ℤ) (hn : n ∈ S) : |a n - b n| ≤ K :=
    coefficient_remainder hN (hS n hn) hm
      (arithmetic_boundary_symbol_bound hc n).2 (arithmetic_boundary_symbol_bound hc m).2
  have heq : couplingColumn c S v m - couplingFirstJet c S v m =
      ∑ n ∈ S, ((a n - b n : ℝ) : ℂ) * v n := by
    unfold couplingColumn couplingFirstJet
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp [a, b]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ∑ n ∈ S, ‖((a n - b n : ℝ) : ℂ) * v n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, K * ‖v n‖ := Finset.sum_le_sum (fun n hn => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hab n hn) (norm_nonneg _))
    _ = _ := by rw [Finset.mul_sum]; rfl

#print axioms arithmetic_boundary_symbol_bound
#print axioms arithmetic_coupling_first_jet_error

end
end D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

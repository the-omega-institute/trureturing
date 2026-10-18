/- GID: D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet
   mirror-E: none(waiver:analytic-estimate-with-separate-interval-certificate)
   anchors: []
   utility: none
   digest: Bound the actual prime-pole-Gamma boundary symbol and its exterior coupling remainder. -/

import D5.S3.Weil.ZetaCore.ExplicitFormula
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

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
def logLength (c : ℕ) : ℝ := Real.log (c : ℝ)
def frequency (c : ℕ) (n : ℤ) : ℝ := 2 * Real.pi * (n : ℝ) / logLength c
def primeWeight (j : ℕ) : ℝ := ArithmeticFunction.vonMangoldt j / Real.sqrt j
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
  have h := mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc)
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
    _ = _ := by rw [Finset.mul_sum]

#print axioms arithmetic_boundary_symbol_bound
#print axioms arithmetic_coupling_first_jet_error

end
end D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/-! Source-only r3033/r3035 append. All preceding owner bytes are preserved.
The weight below is the actual pole plus Gamma sum divided by the mode square.
Only that weight, rather than Gamma itself, is asserted to be antitone. -/
namespace D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
noncomputable section
open scoped BigOperators

private def modeScale (c : ℕ) : ℝ := 2 * Real.pi / logLength c
private def poleCoefficient (c : ℕ) : ℝ :=
  2 * (Real.cosh (logLength c / 2) - 1) / modeScale c

/-- The minimum consumes both the old and the refined Gamma bounds.
Here a=2*pi/log(c), U=2*(cosh(log(c)/2)-1)/a. -/
def smoothEnvelope (c m : ℕ) : ℝ :=
  min (2 + poleCoefficient c / (m : ℝ))
    (Real.pi / 4 + (poleCoefficient c + 3 / (4 * modeScale c)) / (m : ℝ))

/-- Exactly -H_m/m^2, where the actual symbol is A_m=H_m-S_m. -/
def smoothWeight (c m : ℕ) : ℝ :=
  (poleSine (logLength c) (frequency c (m : ℤ)) +
    ∑' j : ℕ, gammaSineTerm (logLength c) (frequency c (m : ℤ)) j) / (m : ℝ) ^ 2

private theorem modeScale_pos {c : ℕ} (hc : 2 ≤ c) : 0 < modeScale c := by
  have hc1 : (1 : ℝ) < c := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hc)
  exact div_pos (by positivity) (Real.log_pos hc1)

private theorem owner_log_pos {c : ℕ} (hc : 2 ≤ c) : 0 < logLength c := by
  apply Real.log_pos
  exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hc)

private theorem frequency_nat (c m : ℕ) :
    frequency c (m : ℤ) = modeScale c * (m : ℝ) := by
  unfold frequency modeScale
  push_cast
  ring

private theorem gamma_factor_nonneg {c : ℕ} (hc : 2 ≤ c) (j : ℕ) :
    0 ≤ 1 - Real.exp (-gammaRate j * logLength c) := by
  apply sub_nonneg.mpr
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (gammaRate_pos j).le)
    (owner_log_pos hc).le

private theorem gamma_positive_summable {c : ℕ} (hc : 2 ≤ c) (m : ℕ) :
    Summable (gammaSineTerm (logLength c) (frequency c (m : ℤ))) :=
  (sineTerm_norm_summable (owner_log_pos hc).le _).of_norm

private theorem gamma_positive_nonneg {c : ℕ} (hc : 2 ≤ c) (m j : ℕ) :
    0 ≤ gammaSineTerm (logLength c) (frequency c (m : ℤ)) j := by
  rw [gammaSineTerm, frequency_nat]
  exact div_nonneg (mul_nonneg (mul_nonneg (modeScale_pos hc).le (Nat.cast_nonneg m))
    (gamma_factor_nonneg hc j)) (by positivity)

section GammaIntegralComparison
open MeasureTheory intervalIntegral
open scoped Interval

/-- Continuous positive Cauchy kernel, only used to sharpen the new envelope. -/
private def gammaKernel (w x : ℝ) : ℝ := w / (w ^ 2 + x ^ 2)

private theorem gammaKernel_continuous {w : ℝ} (hw : 0 < w) :
    Continuous (gammaKernel w) := by
  unfold gammaKernel
  exact continuous_const.div (continuous_const.add (continuous_id.pow 2))
    (fun x => ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hw) (sq_nonneg x)))

private theorem gammaKernel_antitone {w : ℝ} (hw : 0 < w) :
    AntitoneOn (gammaKernel w) (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold gammaKernel
  exact div_le_div_of_nonneg_left hw.le
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hw) (sq_nonneg x))
    (add_le_add le_rfl (pow_le_pow_left₀ hx hxy 2))

/-- The missing quarter correction is the area on [0,1/2], not a
monotonicity assertion about the actual Gamma mass. -/
private theorem gammaKernel_initial_area {w : ℝ} (hw : 0 < w) :
    (1 / 2 : ℝ) * gammaKernel w (1 / 2) ≤ Real.arctan ((1 / 2) / w) := by
  have hfi : IntervalIntegrable (gammaKernel w) MeasureTheory.volume 0 (1 / 2) :=
    (gammaKernel_continuous hw).continuousOn.intervalIntegrable
  calc
    _ = ∫ _ : ℝ in (0 : ℝ)..(1 / 2 : ℝ), gammaKernel w (1 / 2) := by
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    _ ≤ ∫ x : ℝ in (0 : ℝ)..(1 / 2 : ℝ), gammaKernel w x := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) (by simp) hfi
      intro x hx
      exact gammaKernel_antitone hw (le_of_lt hx.1) (by norm_num) (le_of_lt hx.2)
    _ = _ := by
      simp only [gammaKernel, _root_.integral_div_sq_add_sq,
        zero_div, Real.arctan_zero, sub_zero]

/-- Finite integral comparison on the genuine half-shifted Gamma lattice.
The intermediate correction 3*f(1/2)/4 is consumed by the exact target below. -/
private theorem majorant_partial_quarter {w : ℝ} (hw : 0 < w) (M : ℕ) :
    (∑ j ∈ Finset.range M, gammaMajorant w j) ≤
      Real.pi / 4 + (3 / 4 : ℝ) * gammaKernel w (1 / 2) := by
  cases M with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      unfold gammaKernel
      positivity
  | succ M =>
      let g : ℝ → ℝ := fun x => gammaKernel w (2 * x + 1 / 2)
      have hg : AntitoneOn g (Set.Icc (0 : ℝ) (0 + (M : ℝ))) := by
        intro x hx y hy hxy
        apply gammaKernel_antitone hw
        · change 0 ≤ 2 * x + 1 / 2
          linarith [hx.1]
        · change 0 ≤ 2 * y + 1 / 2
          linarith [hy.1]
        · linarith
      have he (j : ℕ) : gammaMajorant w j = g (j : ℝ) := by
        dsimp [gammaMajorant, gammaRate, g, gammaKernel]
        rw [add_comm (w ^ 2)]
      have htail : (∑ j ∈ Finset.range M, gammaMajorant w (j + 1)) ≤
          ∫ x : ℝ in (0 : ℝ)..(M : ℝ), g x := by
        calc
          _ = ∑ j ∈ Finset.range M, g (0 + ((j + 1 : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j _
            simpa only [zero_add] using he (j + 1)
          _ ≤ _ := by simpa only [zero_add] using hg.sum_le_integral
      have hsubst := intervalIntegral.mul_integral_comp_mul_add
        (f := gammaKernel w) (a := (0 : ℝ)) (b := (M : ℝ)) (2 : ℝ) (1 / 2 : ℝ)
      have hint : 2 * (∫ x : ℝ in (0 : ℝ)..(M : ℝ), g x) =
          Real.arctan ((2 * (M : ℝ) + 1 / 2) / w) -
            Real.arctan ((1 / 2) / w) := by
        simpa only [g, mul_zero, zero_add, gammaKernel,
          _root_.integral_div_sq_add_sq] using hsubst
      have hlow := gammaKernel_initial_area hw
      have hhigh := (Real.arctan_lt_pi_div_two ((2 * (M : ℝ) + 1 / 2) / w)).le
      have hz : gammaMajorant w 0 = gammaKernel w (1 / 2) := by
        simp only [gammaMajorant, gammaRate, gammaKernel, Nat.cast_zero,
          mul_zero, zero_add, add_comm]
      rw [Finset.sum_range_succ', hz]
      linarith

private theorem majorant_partial_refined {w : ℝ} (hw : 0 < w) (M : ℕ) :
    (∑ j ∈ Finset.range M, gammaMajorant w j) ≤ Real.pi / 4 + 3 / (4 * w) := by
  have hz : gammaKernel w (1 / 2) ≤ 1 / w := by
    unfold gammaKernel
    apply (div_le_div_iff₀ (by positivity) hw).mpr
    nlinarith
  calc
    _ ≤ Real.pi / 4 + (3 / 4 : ℝ) * gammaKernel w (1 / 2) :=
      majorant_partial_quarter hw M
    _ ≤ Real.pi / 4 + (3 / 4 : ℝ) * (1 / w) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hz (by norm_num))
    _ = _ := by ring

private theorem gamma_positive_refined {L w : ℝ} (hL : 0 ≤ L) (hw : 0 < w) :
    (∑' j : ℕ, gammaSineTerm L w j) ≤ Real.pi / 4 + 3 / (4 * w) := by
  have hs := sineTerm_norm_summable hL w
  calc
    _ ≤ |∑' j : ℕ, gammaSineTerm L w j| := le_abs_self _
    _ ≤ ∑' j : ℕ, ‖gammaSineTerm L w j‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j : ℕ, gammaMajorant w j :=
      hs.tsum_le_tsum (fun j => by
        simpa only [Real.norm_eq_abs, abs_of_pos hw] using sineTerm_abs_le hL w j)
        (majorant_summable hw.le)
    _ ≤ Real.pi / 4 + 3 / (4 * w) :=
      Real.tsum_le_of_sum_range_le (majorant_nonneg hw.le) (majorant_partial_refined hw)


/-! SOURCE_ONLY_UNCOMPILED r3347: the lower comparison is for the genuine
half-shifted majorant, and the removed exponential series is summable. -/

open Filter
open scoped Topology

/-- Left-endpoint rectangles dominate the finite shifted-kernel integral.
The arctan endpoint tends to pi/2; summability permits passage to the actual
majorant sum. The omitted initial half-interval costs at most 1/(4*w). -/
private theorem majorant_tsum_lower {w : ℝ} (hw : 0 < w) :
    Real.pi / 4 - 1 / (4 * w) ≤ ∑' j : ℕ, gammaMajorant w j := by
  let g : ℝ → ℝ := fun x => gammaKernel w (2 * x + 1 / 2)
  have hfinite (M : ℕ) :
      (Real.arctan ((2 * (M : ℝ) + 1 / 2) / w) -
        Real.arctan ((1 / 2) / w)) / 2 ≤ ∑' j : ℕ, gammaMajorant w j := by
    have hg : AntitoneOn g (Set.Icc (0 : ℝ) (0 + (M : ℝ))) := by
      intro x hx y hy hxy
      apply gammaKernel_antitone hw
      · change 0 ≤ 2 * x + 1 / 2
        linarith [hx.1]
      · change 0 ≤ 2 * y + 1 / 2
        linarith [hy.1]
      · linarith
    have he (j : ℕ) : gammaMajorant w j = g (j : ℝ) := by
      dsimp [gammaMajorant, gammaRate, g, gammaKernel]
      rw [add_comm (w ^ 2)]
    have hint_le : (∫ x : ℝ in (0 : ℝ)..(M : ℝ), g x) ≤
        ∑ j ∈ Finset.range M, gammaMajorant w j := by
      calc
        _ ≤ ∑ j ∈ Finset.range M, g (0 + (j : ℝ)) := by
          simpa only [zero_add] using hg.integral_le_sum
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          simpa only [zero_add] using (he j).symm
    have hsubst := intervalIntegral.mul_integral_comp_mul_add
      (f := gammaKernel w) (a := (0 : ℝ)) (b := (M : ℝ)) (2 : ℝ) (1 / 2 : ℝ)
    have hint : 2 * (∫ x : ℝ in (0 : ℝ)..(M : ℝ), g x) =
        Real.arctan ((2 * (M : ℝ) + 1 / 2) / w) -
          Real.arctan ((1 / 2) / w) := by
      simpa only [g, mul_zero, zero_add, gammaKernel,
        _root_.integral_div_sq_add_sq] using hsubst
    have hsum : (∑ j ∈ Finset.range M, gammaMajorant w j) ≤
        ∑' j : ℕ, gammaMajorant w j :=
      Summable.sum_le_tsum (Finset.range M)
        (fun j _ => majorant_nonneg hw.le j) (majorant_summable hw.le)
    linarith
  have hnat : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have harg : Tendsto (fun M : ℕ => (2 * (M : ℝ) + 1 / 2) / w)
      atTop atTop := by
    have hlinear := tendsto_atTop_add_const_right atTop ((1 / 2 : ℝ) / w)
      (hnat.const_mul_atTop (div_pos (by norm_num : (0 : ℝ) < 2) hw))
    convert hlinear using 1 <;> ext M <;> ring
  have hatan : Tendsto (fun M : ℕ =>
      Real.arctan ((2 * (M : ℝ) + 1 / 2) / w)) atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp harg
  have hlim : Tendsto (fun M : ℕ =>
      (Real.arctan ((2 * (M : ℝ) + 1 / 2) / w) -
        Real.arctan ((1 / 2) / w)) / 2) atTop
      (𝓝 ((Real.pi / 2 - Real.arctan ((1 / 2) / w)) / 2)) :=
    (hatan.sub tendsto_const_nhds).div_const (2 : ℝ)
  have hlimit := le_of_tendsto' hlim hfinite
  have hinitial : Real.arctan ((1 / 2 : ℝ) / w) ≤ (1 / 2 : ℝ) / w :=
    Real.arctan_le_self (div_nonneg (by norm_num) hw.le)
  calc
    Real.pi / 4 - 1 / (4 * w) = (Real.pi / 2 - (1 / 2 : ℝ) / w) / 2 := by ring
    _ ≤ (Real.pi / 2 - Real.arctan ((1 / 2 : ℝ) / w)) / 2 := by linarith
    _ ≤ _ := hlimit

private def gammaExpCorrection (L w : ℝ) (j : ℕ) : ℝ :=
  w * Real.exp (-gammaRate j * L) / (gammaRate j ^ 2 + w ^ 2)

/-- The exponential loss is dominated termwise by a positive geometric series.
Both its actual summability and the value of the geometric majorant are used. -/
private theorem gamma_correction_summable_bound {L w : ℝ} (hL : 0 < L) (hw : 0 < w) :
    Summable (gammaExpCorrection L w) ∧
      (∑' j : ℕ, gammaExpCorrection L w j) ≤
        Real.exp (-L / 2) / (w * (1 - Real.exp (-2 * L))) := by
  let q : ℝ := Real.exp (-2 * L)
  let A : ℝ := Real.exp (-L / 2) / w
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hgeom : HasSum (fun j : ℕ => A * q ^ j) (A * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left A
  have hnonneg (j : ℕ) : 0 ≤ gammaExpCorrection L w j := by
    unfold gammaExpCorrection
    exact div_nonneg (mul_nonneg hw.le (Real.exp_pos _).le) (by positivity)
  have hpoint (j : ℕ) : gammaExpCorrection L w j ≤ A * q ^ j := by
    have he : Real.exp (-gammaRate j * L) = Real.exp (-L / 2) * q ^ j := by
      calc
        _ = Real.exp (-L / 2 + (j : ℝ) * (-2 * L)) := by
          congr 1
          dsimp [gammaRate]
          ring
        _ = _ := by simp only [q, Real.exp_add, Real.exp_nat_mul]
    calc
      gammaExpCorrection L w j ≤ w * Real.exp (-gammaRate j * L) / w ^ 2 := by
        unfold gammaExpCorrection
        exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hw)
          (le_add_of_nonneg_left (sq_nonneg _))
      _ = A * q ^ j := by
        rw [he]
        dsimp [A]
        field_simp [hw.ne'] <;> ring
  have hs : Summable (gammaExpCorrection L w) :=
    Summable.of_nonneg_of_le hnonneg hpoint hgeom.summable
  refine ⟨hs, ?_⟩
  calc
    (∑' j : ℕ, gammaExpCorrection L w j) ≤ ∑' j : ℕ, A * q ^ j :=
      hs.tsum_le_tsum hpoint hgeom.summable
    _ = Real.exp (-L / 2) / (w * (1 - Real.exp (-2 * L))) := by
      rw [hgeom.tsum_eq]
      dsimp [A, q]
      simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

/-- Exact subtraction of two genuinely summable series recovers the actual
Gamma sine series. This is a lower estimate for that series, not a new model. -/
private theorem gamma_positive_lower {L w : ℝ} (hL : 0 < L) (hw : 0 < w) :
    Real.pi / 4 -
        (1 / 4 + Real.exp (-L / 2) / (1 - Real.exp (-2 * L))) / w ≤
      ∑' j : ℕ, gammaSineTerm L w j := by
  obtain ⟨hcorr, hbound⟩ := gamma_correction_summable_bound hL hw
  have hmajor := majorant_summable hw.le
  have hidentity : (∑' j : ℕ, gammaSineTerm L w j) =
      (∑' j : ℕ, gammaMajorant w j) - ∑' j : ℕ, gammaExpCorrection L w j := by
    rw [← hmajor.tsum_sub hcorr]
    apply tsum_congr
    intro j
    dsimp [gammaSineTerm, gammaMajorant, gammaExpCorrection]
    ring
  have hden : 0 < 1 - Real.exp (-2 * L) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  have hsplit :
      (1 / 4 + Real.exp (-L / 2) / (1 - Real.exp (-2 * L))) / w =
        1 / (4 * w) + Real.exp (-L / 2) / (w * (1 - Real.exp (-2 * L))) := by
    field_simp [hw.ne', hden.ne'] <;> ring
  rw [hidentity, hsplit]
  linarith [majorant_tsum_lower hw]

end GammaIntegralComparison

private theorem weighted_kernel_antitone {a B r x y : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
    B / (y * (r + (a * y) ^ 2)) ≤ B / (x * (r + (a * x) ^ 2)) := by
  have hp : (a * x) ^ 2 ≤ (a * y) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hxy ha.le) 2
  have hd : x * (r + (a * x) ^ 2) ≤ y * (r + (a * y) ^ 2) :=
    mul_le_mul hxy (add_le_add le_rfl hp) (by positivity) hy.le
  exact div_le_div_of_nonneg_left hB (by positivity) hd

private theorem gamma_weight_eq {c m : ℕ} (hc : 2 ≤ c) (hm : 0 < m) (j : ℕ) :
    gammaSineTerm (logLength c) (frequency c (m : ℤ)) j / (m : ℝ) ^ 2 =
      modeScale c * (1 - Real.exp (-gammaRate j * logLength c)) /
        ((m : ℝ) * (gammaRate j ^ 2 + (modeScale c * (m : ℝ)) ^ 2)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hr := gammaRate_pos j
  have hd : 0 < gammaRate j ^ 2 + (modeScale c * (m : ℝ)) ^ 2 := by positivity
  rw [gammaSineTerm, frequency_nat]
  field_simp [hmR.ne', hd.ne']
  <;> ring

private theorem pole_weight_eq {c m : ℕ} (hc : 2 ≤ c) (hm : 0 < m) :
    poleSine (logLength c) (frequency c (m : ℤ)) / (m : ℝ) ^ 2 =
      (2 * modeScale c * (Real.cosh (logLength c / 2) - 1)) /
        ((m : ℝ) * (1 / 4 + (modeScale c * (m : ℝ)) ^ 2)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : 0 < (modeScale c * (m : ℝ)) ^ 2 + (1 / 4 : ℝ) := by positivity
  rw [poleSine, frequency_nat, add_comm (1 / 4 : ℝ)]
  field_simp [hmR.ne', hd.ne']
  <;> ring

private theorem smooth_weight_series (c m : ℕ) :
    smoothWeight c m =
      poleSine (logLength c) (frequency c (m : ℤ)) / (m : ℝ) ^ 2 +
      ∑' j : ℕ, gammaSineTerm (logLength c) (frequency c (m : ℤ)) j / (m : ℝ) ^ 2 := by
  rw [smoothWeight, add_div, tsum_div_const]

/-- The actual positive-mode smooth weight is nonnegative. -/
theorem smooth_weight_nonneg {c m : ℕ} (hc : 2 ≤ c) (hm : 0 < m) :
    0 ≤ smoothWeight c m := by
  rw [smooth_weight_series, pole_weight_eq hc hm]
  apply add_nonneg
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (modeScale_pos hc).le)
      (sub_nonneg.mpr (Real.one_le_cosh _))) (by positivity)
  · exact tsum_nonneg (fun j => div_nonneg (gamma_positive_nonneg hc m j) (sq_nonneg _))

/-- Monotonicity belongs to -H_m/m^2, with the convergent Gamma sums retained. -/
theorem smooth_weight_antitone {c n m : ℕ} (hc : 2 ≤ c)
    (hn : 0 < n) (hnm : n ≤ m) : smoothWeight c m ≤ smoothWeight c n := by
  have hm : 0 < m := lt_of_lt_of_le hn hnm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  rw [smooth_weight_series, smooth_weight_series, pole_weight_eq hc hm, pole_weight_eq hc hn]
  apply add_le_add
  · exact weighted_kernel_antitone (modeScale_pos hc)
      (mul_nonneg (mul_nonneg (by norm_num) (modeScale_pos hc).le)
        (sub_nonneg.mpr (Real.one_le_cosh _))) (by norm_num) hnR hmR hnmR
  · apply ((gamma_positive_summable hc m).div_const ((m : ℝ) ^ 2)).tsum_le_tsum
      (fun j => ?_) ((gamma_positive_summable hc n).div_const ((n : ℝ) ^ 2))
    rw [gamma_weight_eq hc hm, gamma_weight_eq hc hn]
    exact weighted_kernel_antitone (modeScale_pos hc)
      (mul_nonneg (modeScale_pos hc).le (gamma_factor_nonneg hc j))
      (sq_nonneg _) hnR hmR hnmR

private theorem pole_positive_bound {c m : ℕ} (hc : 2 ≤ c) (hm : 0 < m) :
    poleSine (logLength c) (frequency c (m : ℤ)) ≤ poleCoefficient c / (m : ℝ) := by
  have ha := modeScale_pos hc
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : 0 ≤ Real.cosh (logLength c / 2) - 1 := sub_nonneg.mpr (Real.one_le_cosh _)
  rw [poleSine, frequency_nat]
  calc
    _ ≤ 2 * (modeScale c * (m : ℝ)) * (Real.cosh (logLength c / 2) - 1) /
        (modeScale c * (m : ℝ)) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ = _ := by
      unfold poleCoefficient
      field_simp [ha.ne', hmR.ne']
      <;> ring

private theorem smooth_mass_bounds {c m : ℕ} (hc : 2 ≤ c) (hm : 0 < m) :
    (m : ℝ) ^ 2 * smoothWeight c m ≤ 2 + poleCoefficient c / (m : ℝ) ∧
    (m : ℝ) ^ 2 * smoothWeight c m ≤
      Real.pi / 4 + (poleCoefficient c + 3 / (4 * modeScale c)) / (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ha := modeScale_pos hc
  have heq : (m : ℝ) ^ 2 * smoothWeight c m =
      poleSine (logLength c) (frequency c (m : ℤ)) +
      ∑' j : ℕ, gammaSineTerm (logLength c) (frequency c (m : ℤ)) j := by
    unfold smoothWeight
    field_simp [hmR.ne']
  rw [heq]
  have hp := pole_positive_bound hc hm
  have hg := gamma_sine_abs_le_two (owner_log_pos hc).le (frequency c (m : ℤ))
  have hgr := gamma_positive_refined (owner_log_pos hc).le (mul_pos ha hmR)
  rw [← frequency_nat] at hgr
  constructor
  · linarith [le_abs_self (∑' j : ℕ, gammaSineTerm (logLength c) (frequency c (m : ℤ)) j)]
  · have hi : 3 / (4 * frequency c (m : ℤ)) + poleCoefficient c / (m : ℝ) =
        (poleCoefficient c + 3 / (4 * modeScale c)) / (m : ℝ) := by
      rw [frequency_nat]
      field_simp [ha.ne', hmR.ne']
      <;> ring
    linarith

/-- A single envelope theorem consumes both Gamma bounds. At every m>=n>0,
0<=E(c,n) and m^2*w(c,m)<=E(c,n). No small-cutoff assumption is used. -/
theorem smooth_weight_envelope {c n m : ℕ} (hc : 2 ≤ c)
    (hn : 0 < n) (hnm : n ≤ m) :
    0 ≤ smoothEnvelope c n ∧ (m : ℝ) ^ 2 * smoothWeight c m ≤ smoothEnvelope c n := by
  have hm := lt_of_lt_of_le hn hnm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have ha := modeScale_pos hc
  have hU : 0 ≤ poleCoefficient c :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_cosh _))) ha.le
  obtain ⟨h2, h1⟩ := smooth_mass_bounds hc hm
  constructor
  · unfold smoothEnvelope
    exact le_min (by positivity) (by positivity)
  · unfold smoothEnvelope
    apply le_min
    · exact h2.trans (add_le_add le_rfl
        (div_le_div_of_nonneg_left hU hnR hnmR))
    · exact h1.trans (add_le_add le_rfl
        (div_le_div_of_nonneg_left
          (show 0 ≤ poleCoefficient c + 3 / (4 * modeScale c) from
            add_nonneg hU (by positivity)) hnR hnmR))

/-- Exact A=H-S split using only owner definitions. The downstream module
identifies this finite sum with T2.primeSymbol without creating an import cycle. -/
theorem arithmetic_symbol_smooth_split (c : ℕ) {m : ℕ} (hm : 0 < m) :
    arithmeticBoundarySymbol c (m : ℤ) = -(m : ℝ) ^ 2 * smoothWeight c m -
      ∑ q ∈ Finset.range c, primeWeight q * Real.sin (frequency c (m : ℤ) * Real.log q) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold arithmeticBoundarySymbol smoothWeight
  field_simp [hmR.ne']
  <;> ring

/- SOURCE_ONLY_UNCOMPILED.
Splice inside the existing Jet namespace and noncomputable section, after
arithmetic_symbol_smooth_split and before the final two ends. Header additions:
  import Mathlib.Algebra.Order.Floor.Semiring
  import Mathlib.Algebra.Order.Archimedean.Real.Basic
All private operands remain in their original physical source owner.

Sign convention here: H_m = m^2 * smoothWeight c m is the POSITIVE smooth
mass, and the actual arithmetic symbol is A_m = -H_m - S_m. Some older owner
comments use the negative H convention; no such convention is used below.
-/

/-- An explicit positive finite-block floor for the actual smooth mass. -/
def smoothFloor (c : ℕ) : ℝ := (1 - Real.exp (-logLength c / 2)) / 10

private theorem gamma_finite_block_floor {c m : ℕ} (hc : 2 ≤ c)
    (hw : 1 ≤ frequency c (m : ℤ)) :
    0 < smoothFloor c ∧
      smoothFloor c ≤
        ∑' j : ℕ, gammaSineTerm (logLength c) (frequency c (m : ℤ)) j := by
  let L : ℝ := logLength c
  let w : ℝ := frequency c (m : ℤ)
  let eta : ℝ := 1 - Real.exp (-L / 2)
  let N : ℕ := Nat.ceil w
  have hL : 0 < L := owner_log_pos hc
  have hw1 : 1 ≤ w := hw
  have hw0 : 0 < w := by linarith
  have heta : 0 < eta := by
    dsimp [eta]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hsmall : 0 ≤ eta / (10 * w) :=
    (div_pos heta (mul_pos (by norm_num) hw0)).le
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      eta / (10 * w) ≤ gammaSineTerm L w j := by
    have hjw : (j : ℝ) < w :=
      Nat.lt_ceil.mp (show j < Nat.ceil w from Finset.mem_range.mp hj)
    have hg : 0 < gammaRate j := gammaRate_pos j
    have hhalf : (1 / 2 : ℝ) ≤ gammaRate j := by
      unfold gammaRate
      linarith [Nat.cast_nonneg (α := ℝ) j]
    have hg3 : gammaRate j ≤ 3 * w := by
      unfold gammaRate
      linarith
    have hden : 0 < gammaRate j ^ 2 + w ^ 2 := by positivity
    have hdenle : gammaRate j ^ 2 + w ^ 2 ≤ 10 * w ^ 2 := by
      have hsquare := pow_le_pow_left₀ hg.le hg3 2
      nlinarith only [hsquare]
    have hfactor : eta ≤ 1 - Real.exp (-gammaRate j * L) := by
      have hproduct := mul_le_mul_of_nonneg_right hhalf hL.le
      have harg : -gammaRate j * L ≤ -L / 2 := by
        nlinarith only [hproduct]
      dsimp [eta]
      exact sub_le_sub_left (Real.exp_le_exp.mpr harg) 1
    -- Two separate division comparisons: first denominators, then numerators.
    calc
      eta / (10 * w) = w * eta / (10 * w ^ 2) := by
        field_simp [hw0.ne'] <;> ring
      _ ≤ w * eta / (gammaRate j ^ 2 + w ^ 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hw0.le heta.le) hden hdenle
      _ ≤ gammaSineTerm L w j := by
        unfold gammaSineTerm
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactor hw0.le) hden.le
  have hwN : w ≤ (N : ℝ) := Nat.le_ceil w
  have hblock : eta / 10 ≤ ∑ j ∈ Finset.range N, gammaSineTerm L w j := by
    calc
      eta / 10 = w * (eta / (10 * w)) := by
        field_simp [hw0.ne'] <;> ring
      _ ≤ (N : ℝ) * (eta / (10 * w)) :=
        mul_le_mul_of_nonneg_right hwN hsmall
      _ = ∑ _j ∈ Finset.range N, eta / (10 * w) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range N, gammaSineTerm L w j :=
        Finset.sum_le_sum hterm
  -- This is the genuine convergent owner series, after the finite-block bound.
  have hinfinite :
      (∑ j ∈ Finset.range N, gammaSineTerm L w j) ≤
        ∑' j : ℕ, gammaSineTerm L w j :=
    Summable.sum_le_tsum (Finset.range N)
      (fun j _ => gamma_positive_nonneg hc m j)
      (gamma_positive_summable hc m)
  change 0 < eta / 10 ∧ eta / 10 ≤ ∑' j : ℕ, gammaSineTerm L w j
  exact ⟨div_pos heta (by norm_num), hblock.trans hinfinite⟩

/-- For every c>=2 and positive natural mode with frequency at least one,
the actual positive mass H_m=m^2*smoothWeight(c,m) has the explicit floor.
The proof retains the native pole and genuinely summable Gamma series. -/
theorem smooth_weight_floor {c m : ℕ} (hc : 2 ≤ c) (hm : 0 < m)
    (hw : 1 ≤ frequency c (m : ℤ)) :
    0 < smoothFloor c ∧ smoothFloor c ≤ (m : ℝ) ^ 2 * smoothWeight c m := by
  obtain ⟨hpositive, hgamma⟩ := gamma_finite_block_floor hc hw
  have hw0 : 0 ≤ frequency c (m : ℤ) := le_trans (by norm_num) hw
  have hpole : 0 ≤ poleSine (logLength c) (frequency c (m : ℤ)) := by
    unfold poleSine
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hw0)
        (sub_nonneg.mpr (Real.one_le_cosh _))) (by positivity)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- The same cancellation pattern as the existing smooth_mass_bounds.
  have heq : (m : ℝ) ^ 2 * smoothWeight c m =
      poleSine (logLength c) (frequency c (m : ℤ)) +
      ∑' j : ℕ, gammaSineTerm (logLength c) (frequency c (m : ℤ)) j := by
    unfold smoothWeight
    field_simp [hmR.ne']
  refine ⟨hpositive, ?_⟩
  rw [heq]
  linarith


/-- For every fixed natural cutoff c>=2 the actual smooth mass approaches pi/4
with an O(1/m) error, at every positive natural mode. The constant is chosen
before m; no frequency threshold, cutoff restriction, or tail/RH claim enters. -/
theorem smooth_weight_actual_asymptotic (c : ℕ) (hc : 2 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m →
      |(m : ℝ) ^ 2 * smoothWeight c m - Real.pi / 4| ≤ K / (m : ℝ) := by
  let C : ℝ := Real.exp (-logLength c / 2) /
    (1 - Real.exp (-2 * logLength c))
  let K : ℝ := poleCoefficient c + (1 + C) / modeScale c
  have hL := owner_log_pos hc
  have ha := modeScale_pos hc
  have hden : 0 < 1 - Real.exp (-2 * logLength c) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  have hC : 0 ≤ C := (div_pos (Real.exp_pos _) hden).le
  have hU : 0 ≤ poleCoefficient c :=
    div_nonneg (mul_nonneg (by norm_num)
      (sub_nonneg.mpr (Real.one_le_cosh _))) ha.le
  have hK : 0 < K :=
    add_pos_of_nonneg_of_pos hU (div_pos (by linarith) ha)
  have hupper_constant : poleCoefficient c + 3 / (4 * modeScale c) ≤ K := by
    have h := div_le_div_of_nonneg_right
      (show (3 / 4 : ℝ) ≤ 1 + C by linarith) ha.le
    have he : (3 / 4 : ℝ) / modeScale c = 3 / (4 * modeScale c) := by ring
    rw [he] at h
    dsimp [K]
    linarith
  have hlower_constant : (1 / 4 + C) / modeScale c ≤ K := by
    have h := div_le_div_of_nonneg_right
      (show (1 / 4 : ℝ) + C ≤ 1 + C by linarith) ha.le
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  intro m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hw : 0 < frequency c (m : ℤ) := by
    rw [frequency_nat]
    exact mul_pos ha hmR
  have hgamma := gamma_positive_lower hL hw
  change Real.pi / 4 - (1 / 4 + C) / frequency c (m : ℤ) ≤ _ at hgamma
  have hscale : (1 / 4 + C) / frequency c (m : ℤ) =
      ((1 / 4 + C) / modeScale c) / (m : ℝ) := by
    simp only [frequency_nat, div_mul_eq_div_div]
  rw [hscale] at hgamma
  have hpole : 0 ≤ poleSine (logLength c) (frequency c (m : ℤ)) := by
    unfold poleSine
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hw.le)
        (sub_nonneg.mpr (Real.one_le_cosh _))) (by positivity)
  have hmass : (m : ℝ) ^ 2 * smoothWeight c m =
      poleSine (logLength c) (frequency c (m : ℤ)) +
      ∑' j : ℕ, gammaSineTerm (logLength c) (frequency c (m : ℤ)) j := by
    unfold smoothWeight
    field_simp [hmR.ne']
  apply abs_le.mpr
  constructor
  · have h := div_le_div_of_nonneg_right hlower_constant hmR.le
    rw [hmass]
    linarith
  · have hmass_upper := (smooth_mass_bounds hc hm).2
    have h := div_le_div_of_nonneg_right hupper_constant hmR.le
    linarith

end
end D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

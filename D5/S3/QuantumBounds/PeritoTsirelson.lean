/- GID: D5/S3/QuantumBounds/PeritoTsirelson
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/PeritoTsirelson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: State the finite-dimensional Perito Bell bound and its explicit attaining strategy. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.QuantumBounds.PeritoUnitCircleSum
import D5.S3.QuantumBounds.PeritoTensorBlockBound
import D5.S3.Quantum.Algebra.WeylDisplacementTrace
import D5.S3.Quantum.Algebra.WeylDisplacementPowers
import Mathlib.FieldTheory.KummerExtension
import D5.S3.Weil.ZetaLinear.RankTrace

/-!
# Perito Bell functional

The outcome count is `d`, Alice has two settings, and Bob has `d` settings.
The dimensions of their Hilbert spaces are independent of the outcome count.
The conjecture includes validity and attainment of the cyclic strategy.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Observer.WindowRegister
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylDisplacementTrace

namespace D5.S3.QuantumBounds.PeritoTsirelson

/-- Appendix coefficients, with the negative exponent taken in `ℤ`. -/
def peritoLambda (d : ℕ) (y k : Fin d) : ℂ :=
  ((-1 : ℂ) ^ k.val * windowRoot d ^ (k.val * (k.val + 1) / 2) *
      windowRoot d ^ (-(y.val * (1 + k.val) : ℤ))) /
    ((d : ℂ) * (Real.sin (Real.pi / (d : ℝ) * ((k.val : ℝ) + 1 / 2)) : ℂ))

/-- Bob's appendix observable in the existing cyclic clock and shift basis. -/
def peritoB (d : ℕ) [NeZero d] (y : Fin d) : Matrix (ZMod d) (ZMod d) ℂ :=
  ∑ k : Fin d, peritoLambda d y k • (shiftMatrix d ^ (k.val + 1) * clockMatrix d ^ k.val)


private theorem root_triangular (d : ℕ) [NeZero d] :
    windowRoot d ^ ((d - 1) * d / 2) = (-1 : ℂ) ^ (d - 1) := by
  have hd : 0 < d := NeZero.pos d
  have he : 2 ∣ (d - 1) * d := by
    simpa [Nat.sub_add_cancel hd] using (Nat.even_mul_succ_self (d - 1)).two_dvd
  have hmul : (d - 1) * d / 2 * 2 = (d - 1) * d := Nat.div_mul_cancel he
  have hc : (((d - 1) * d / 2 : ℕ) : ℂ) * 2 = ((d - 1 : ℕ) : ℂ) * (d : ℂ) := by
    exact_mod_cast hmul
  rw [windowRoot, ← Complex.exp_nat_mul, ← Complex.exp_pi_mul_I,
    ← Complex.exp_nat_mul]
  congr 1
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  field_simp [hdn]
  simpa [mul_comm] using hc

private theorem trace_powers (d : ℕ) [NeZero d] (n m : ℕ) :
    Matrix.trace (shiftMatrix d ^ n * clockMatrix d ^ m) =
      if (n : ZMod d) = 0 ∧ (m : ZMod d) = 0 then (d : ℂ) else 0 := by
  have heq : shiftMatrix d ^ n * clockMatrix d ^ m =
      displacement d (n : ZMod d) (m : ZMod d) := by
    rw [displacement, ZMod.val_natCast, ZMod.val_natCast,
      shiftMatrix_pow_mod, clockMatrix_pow_mod]
  rw [heq, displacement_trace]

private theorem shift_transpose_mul (d : ℕ) [NeZero d] :
    (shiftMatrix d)ᵀ * shiftMatrix d = 1 := by
  have heq : (shiftMatrix d)ᵀ = star (shiftMatrix d) := by
    ext i j
    simp [shiftMatrix,
      Matrix.circulant_apply]
  rw [heq]
  exact (window_unitary (M := d)).1

private theorem trace_clock_word (d : ℕ) [NeZero d] (k : Fin d) :
    Matrix.trace ((clockMatrix d)ᵀ *
      (shiftMatrix d ^ (k.val + 1) * clockMatrix d ^ k.val)) =
      if k.val + 1 = d then (d : ℂ) else 0 := by
  rw [clockMatrix, Matrix.diagonal_transpose]
  change Matrix.trace (clockMatrix d *
    (shiftMatrix d ^ (k.val + 1) * clockMatrix d ^ k.val)) = _
  rw [Matrix.trace_mul_comm (clockMatrix d), mul_assoc, ← pow_succ]
  rw [trace_powers]
  congr 1
  apply propext
  simp only [and_self, ZMod.natCast_eq_zero_iff]
  exact ⟨fun h => Nat.le_antisymm (by omega) (Nat.le_of_dvd (by omega) h),
    fun h => by rw [h]⟩

private theorem trace_shift_word (d : ℕ) [NeZero d] (k : Fin d) :
    Matrix.trace ((shiftMatrix d)ᵀ *
      (shiftMatrix d ^ (k.val + 1) * clockMatrix d ^ k.val)) =
      if k.val = 0 then (d : ℂ) else 0 := by
  rw [pow_succ', ← mul_assoc, ← mul_assoc, shift_transpose_mul, one_mul,
    trace_powers]
  congr 1
  apply propext
  simp only [and_self, ZMod.natCast_eq_zero_iff]
  exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h k.isLt, fun h => h ▸ dvd_zero d⟩

private theorem lambda_zero (d : ℕ) [NeZero d] (y : Fin d) :
    peritoLambda d y 0 = windowRoot d ^ (-(y.val : ℤ)) /
      ((d : ℂ) * (Real.sin (Real.pi / (2 * (d : ℝ))) : ℂ)) := by
  simp only [peritoLambda, Fin.val_zero, pow_zero, one_mul, Int.natCast_zero,
    add_zero, mul_one]
  norm_num
  congr 3
  ring

private theorem lambda_last (d : ℕ) [NeZero d] (hd : 2 ≤ d) (y : Fin d) :
    peritoLambda d y ⟨d - 1, by omega⟩ =
      1 / ((d : ℂ) * (Real.sin (Real.pi / (2 * (d : ℝ))) : ℂ)) := by
  have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hlast : (d - 1) + 1 = d := by omega
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have hh : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by exact_mod_cast hlast
    linarith
  have hphase : windowRoot d ^ (-(y.val * (1 + (d - 1 : ℕ)) : ℤ)) = 1 := by
    have hexp : -(y.val * (1 + (d - 1 : ℕ)) : ℤ) = -(y.val : ℤ) * (d : ℤ) := by
      have hh : (1 : ℤ) + ((d - 1 : ℕ) : ℤ) = (d : ℤ) := by
        exact_mod_cast (show 1 + (d - 1) = d by omega)
      rw [hh]; ring
    rw [hexp, mul_comm, zpow_mul, zpow_natCast,
      (windowRoot_isPrimitiveRoot d).pow_eq_one, one_zpow]
  simp only [peritoLambda, hlast, hphase, mul_one, root_triangular]
  have hsign : (-1 : ℂ) ^ (d - 1) * (-1 : ℂ) ^ (d - 1) = 1 := by
    rw [← mul_pow]; simp
  rw [hsign]
  congr 2
  congr 1
  rw [hcast]
  have harg : Real.pi / (d : ℝ) * ((d : ℝ) - 1 + 1 / 2) =
      Real.pi - Real.pi / (2 * (d : ℝ)) := by field_simp; ring
  rw [harg, Real.sin_pi_sub]

private theorem trace_clock_B (d : ℕ) [NeZero d] (hd : 2 ≤ d) (y : Fin d) :
    Matrix.trace ((clockMatrix d)ᵀ * peritoB d y) =
      1 / (Real.sin (Real.pi / (2 * (d : ℝ))) : ℂ) := by
  let last : Fin d := ⟨d - 1, by omega⟩
  rw [peritoB, Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_clock_word]
  rw [Finset.sum_eq_single last]
  · have hh : last.val + 1 = d := by dsimp [last]; omega
    rw [if_pos hh, lambda_last d hd]
    have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
    field_simp
  · intro k hk hkl
    have hh : k.val + 1 ≠ d := by
      intro hh; apply hkl; apply Fin.ext; dsimp [last]; omega
    simp [hh]
  · simp

private theorem trace_shift_B (d : ℕ) [NeZero d] (y : Fin d) :
    Matrix.trace ((shiftMatrix d)ᵀ * peritoB d y) =
      windowRoot d ^ (-(y.val : ℤ)) /
        (Real.sin (Real.pi / (2 * (d : ℝ))) : ℂ) := by
  rw [peritoB, Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_shift_word]
  rw [Finset.sum_eq_single (0 : Fin d)]
  · rw [Fin.val_zero, if_pos rfl, lambda_zero]
    have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
    field_simp
  · intro k hk hk0
    have hh : k.val ≠ 0 := by
      intro hv; apply hk0; apply Fin.ext; simpa using hv
    simp [hh]
  · simp

/-- The two transposed-generator traces give the same positive contribution. -/
private theorem peritoB_attained_term (d : ℕ) [NeZero d] (hd : 2 ≤ d) (y : Fin d) :
    Matrix.trace ((clockMatrix d)ᵀ * peritoB d y) +
      windowRoot d ^ y.val * Matrix.trace ((shiftMatrix d)ᵀ * peritoB d y) =
        ((2 / Real.sin (Real.pi / (2 * (d : ℝ))) : ℝ) : ℂ) := by
  rw [trace_clock_B d hd, trace_shift_B]
  have hroot : windowRoot d ≠ 0 := (windowRoot_isPrimitiveRoot d).ne_zero (NeZero.ne d)
  rw [← mul_div_assoc, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hroot)]
  push_cast
  ring

/-- Sum of the attained traces before division by the state dimension. -/
theorem peritoB_attained_sum (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∑ y : Fin d, (Matrix.trace ((clockMatrix d)ᵀ * peritoB d y) +
      windowRoot d ^ y.val * Matrix.trace ((shiftMatrix d)ᵀ * peritoB d y))) =
        (d : ℂ) * ((2 / Real.sin (Real.pi / (2 * (d : ℝ))) : ℝ) : ℂ) := by
  calc
    _ = ∑ _y : Fin d, (((2 / Real.sin (Real.pi / (2 * (d : ℝ))) : ℝ) : ℂ)) :=
      Finset.sum_congr rfl (fun y _ => peritoB_attained_term d hd y)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private def fourierPhase (d : ℕ) (j : ZMod d) : ℂ :=
  Complex.I * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((j.val : ℂ) + 1 / 2) / d))

private theorem char_exp (d : ℕ) [NeZero d] (j k : ZMod d) :
    ZMod.stdAddChar (-(j * k)) =
      Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * j.val * k.val / d)) := by
  conv_lhs => rw [← j.natCast_zmod_val, ← k.natCast_zmod_val, ← Nat.cast_mul,
    ← Int.cast_natCast, ← Int.cast_neg, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private theorem half_ratio_pow (d : ℕ) [NeZero d] (k : ℕ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I * (2 * k + 1) / d)) ^ d = -1 := by
  have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  rw [← Complex.exp_nat_mul]
  have hh : (d : ℂ) * (-((Real.pi : ℂ) * Complex.I * (2 * k + 1) / d)) =
      ((2 * k + 1 : ℕ) : ℂ) * (-(Real.pi : ℂ) * Complex.I) := by
    push_cast; field_simp
  rw [hh, Complex.exp_nat_mul]
  rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  simp [pow_add, pow_mul]

private theorem fin_val (d : ℕ) [NeZero d] (k : Fin d) :
    ((ZMod.finEquiv d).toEquiv k).val = k.val := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d => rfl

private theorem geom_ZMod (d : ℕ) [NeZero d] (r : ℂ) (hr : r ≠ 1) :
    (∑ j : ZMod d, r ^ j.val) = (r ^ d - 1) / (r - 1) := by
  rw [← (ZMod.finEquiv d).toEquiv.sum_comp (fun j : ZMod d => r ^ j.val)]
  have hsum : (∑ j : Fin d, r ^ ((ZMod.finEquiv d).toEquiv j).val) =
      ∑ j : Fin d, r ^ j.val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [fin_val]
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range]
  exact geom_sum_eq hr d

private theorem phase_dft (d : ℕ) [NeZero d] (k : ZMod d) :
    ZMod.dft (fourierPhase d) k =
      Complex.exp ((Real.pi : ℂ) * Complex.I * k.val / d) /
        (Real.sin (Real.pi / d * ((k.val : ℝ) + 1 / 2)) : ℂ) := by
  let r : ℂ := Complex.exp (-((Real.pi : ℂ) * Complex.I * (2 * k.val + 1) / d))
  have hrpow : r ^ d = -1 := half_ratio_pow d k.val
  have hr : r ≠ 1 := by intro hh; rw [hh, one_pow] at hrpow; norm_num at hrpow
  have hexp (j : ZMod d) : ZMod.stdAddChar (-(j * k)) * fourierPhase d j =
      (Complex.I * Complex.exp (-((Real.pi : ℂ) * Complex.I / (2 * d)))) * r ^ j.val := by
    rw [char_exp, fourierPhase]
    dsimp [r]
    rw [← Complex.exp_nat_mul]
    rw [mul_left_comm]
    simp only [mul_assoc]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 2
    ring
  rw [ZMod.dft_apply]
  simp_rw [smul_eq_mul, hexp]
  rw [← Finset.mul_sum, geom_ZMod d r hr, hrpow]
  let a : ℝ := Real.pi / d * ((k.val : ℝ) + 1 / 2)
  have hdp : (0 : ℝ) < d := by exact_mod_cast (NeZero.pos d)
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hak : (k.val : ℝ) + 1 / 2 < (d : ℝ) := by
    have hh : (k.val : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast k.val_lt
    linarith
  have haπ : a < Real.pi := by
    calc
      a < Real.pi / d * d := mul_lt_mul_of_pos_left hak (by positivity)
      _ = Real.pi := div_mul_cancel₀ _ (ne_of_gt hdp)
  have hsin : (Real.sin a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ha0 haπ))
  have hden : 1 - r = 2 * Complex.I * Complex.exp (-(a : ℂ) * Complex.I) *
      (Real.sin a : ℂ) := by
    have hrform : r = Complex.exp (-2 * (a : ℂ) * Complex.I) := by
      dsimp [r, a]; push_cast; congr 1; ring
    rw [hrform]
    rw [show -2 * (a : ℂ) * Complex.I = -(a : ℂ) * Complex.I +
      -(a : ℂ) * Complex.I by ring, Complex.exp_add]
    rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I, Real.sin_neg, Real.cos_neg]
    have htrig : (Real.cos a : ℂ) ^ 2 + (Real.sin a : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq a
    push_cast
    linear_combination (norm := (ring_nf; simp [Complex.I_sq])) -htrig
  have hnum : Complex.I * Complex.exp (-((Real.pi : ℂ) * Complex.I / (2 * d))) =
      Complex.exp ((Real.pi : ℂ) * Complex.I * k.val / d) *
        Complex.I * Complex.exp (-(a : ℂ) * Complex.I) := by
    rw [mul_assoc, mul_left_comm, ← Complex.exp_add]
    congr 2
    dsimp [a]; push_cast; ring
  rw [hnum, ← mul_div_assoc]
  have hrne : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  apply (div_eq_div_iff hrne hsin).2
  have hh := hden
  dsimp [a] at hh ⊢
  linear_combination Complex.exp ((Real.pi : ℂ) * Complex.I * k.val / d) * hh
private theorem char_exp_pos (d : ℕ) [NeZero d] (j k : ZMod d) :
    ZMod.stdAddChar (j * k) =
      Complex.exp ((2 : ℂ) * Real.pi * Complex.I * j.val * k.val / d) := by
  apply inv_injective
  rw [← AddChar.map_neg_eq_inv, char_exp, ← Complex.exp_neg]

def peritoNu (d : ℕ) (j : ZMod d) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (2 * j.val + 1) / d)

def peritoG (d : ℕ) (z : ℂ) : ℂ :=
  ∑ k : Fin d, z ^ k.val /
    ((d : ℂ) * (Real.sin (Real.pi / d * ((k.val : ℝ) + 1 / 2)) : ℂ))

private theorem peritoG_peritoNu (d : ℕ) [NeZero d] (j : ZMod d) :
    peritoG d (peritoNu d j) = fourierPhase d j := by
  have hinv := congrFun ((ZMod.dft (N := d) (E := ℂ)).symm_apply_apply (fourierPhase d)) j
  rw [ZMod.invDFT_apply] at hinv
  calc
    peritoG d (peritoNu d j) =
        (d : ℂ)⁻¹ * ∑ k : ZMod d, ZMod.stdAddChar (k * j) *
          ZMod.dft (fourierPhase d) k := by
      rw [peritoG, Finset.mul_sum]
      refine Fintype.sum_equiv (ZMod.finEquiv d).toEquiv _ _ ?_
      intro k
      have he : peritoNu d j ^ k.val =
          ZMod.stdAddChar (((ZMod.finEquiv d) k) * j) *
            Complex.exp ((Real.pi : ℂ) * Complex.I * k.val / d) := by
        rw [char_exp_pos, peritoNu, ← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        rw [show ((ZMod.finEquiv d) k).val = k.val from fin_val d k]
        change (k.val : ℂ) * ((Real.pi : ℂ) * Complex.I * (2 * j.val + 1) / d) =
          2 * Real.pi * Complex.I * k.val * j.val / d +
            (Real.pi : ℂ) * Complex.I * k.val / d
        ring
      rw [he, phase_dft, fin_val]
      change _ = (d : ℂ)⁻¹ * (ZMod.stdAddChar (((ZMod.finEquiv d) k) * j) *
        (Complex.exp ((Real.pi : ℂ) * Complex.I * k.val / d) /
          (Real.sin (Real.pi / d * ((k.val : ℝ) + 1 / 2)) : ℂ)))
      ring
    _ = fourierPhase d j := by simpa [smul_eq_mul] using hinv

private theorem phase_centered (d : ℕ) [NeZero d] (j : ZMod d) :
    fourierPhase d j = Complex.exp (((Real.pi : ℂ) / (2 * d)) *
      ((d : ℂ) - 1 - 2 * j.val) * Complex.I) := by
  rw [fourierPhase]
  conv_lhs => lhs; rw [← Complex.exp_pi_div_two_mul_I]
  rw [← Complex.exp_add]
  congr 1
  have hdn : (d : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  field_simp
  ring

/-- Finite Fourier inversion evaluates the cosecant polynomial at every root of minus one. -/
theorem peritoG_at_nu (d : ℕ) [NeZero d] (j : ZMod d) :
    peritoG d (peritoNu d j) = Complex.exp (((Real.pi : ℂ) / (2 * d)) *
      ((d : ℂ) - 1 - 2 * j.val) * Complex.I) := by
  rw [peritoG_peritoNu, phase_centered]

private theorem peritoNu_factor (d : ℕ) [NeZero d] (j : ZMod d) :
    peritoNu d j = windowRoot d ^ j.val * Complex.exp ((Real.pi : ℂ) * Complex.I / d) := by
  rw [peritoNu, windowRoot, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

private theorem peritoNu_pow (d : ℕ) [NeZero d] (j : ZMod d) :
    peritoNu d j ^ d = -1 := by
  have hh := congrArg Inv.inv (half_ratio_pow d j.val)
  simpa [peritoNu, Complex.exp_neg, inv_pow] using hh

private theorem polynomial_roots_dvd (d : ℕ) [NeZero d] (p : Polynomial ℂ)
    (hp : ∀ j : ZMod d, p.eval (peritoNu d j) = 0) :
    (Polynomial.X ^ d + 1) ∣ p := by
  have hprod := X_pow_sub_C_eq_prod (windowRoot_isPrimitiveRoot d) (NeZero.pos d)
    (peritoNu_pow d 0)
  have hz : peritoNu d (0 : ZMod d) = Complex.exp ((Real.pi : ℂ) * Complex.I / d) := by
    simp [peritoNu]
  rw [hz, Polynomial.C_neg, Polynomial.C_1, sub_neg_eq_add] at hprod
  rw [hprod]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro i hi j hj hij
    have hne : windowRoot d ^ i * Complex.exp ((Real.pi : ℂ) * Complex.I / d) ≠
        windowRoot d ^ j * Complex.exp ((Real.pi : ℂ) * Complex.I / d) := by
      intro hh
      have hpow := mul_right_cancel₀ (Complex.exp_ne_zero _) hh
      exact hij ((windowRoot_isPrimitiveRoot d).pow_inj
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hpow)
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hne).isUnit
  · intro i hi
    apply Polynomial.dvd_iff_isRoot.mpr
    change p.eval _ = 0
    have hh := hp (i : ZMod d)
    rw [peritoNu_factor, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)] at hh
    exact hh

private theorem matrix_polynomial_eq (d : ℕ) [NeZero d]
    (u : Matrix (ZMod d) (ZMod d) ℂ) (hu : u ^ d = -1)
    (p q : Polynomial ℂ)
    (hpq : ∀ j : ZMod d, p.eval (peritoNu d j) = q.eval (peritoNu d j)) :
    Polynomial.aeval u p = Polynomial.aeval u q := by
  have hdvd := polynomial_roots_dvd d (p - q) (by
    intro j; simp only [Polynomial.eval_sub, hpq, sub_self])
  have hzero : Polynomial.aeval u (Polynomial.X ^ d + 1 : Polynomial ℂ) = 0 := by
    simp [hu]
  have hh := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hzero
  simpa only [map_sub, sub_eq_zero] using hh

private theorem shift_clock_pow (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (shiftMatrix d * clockMatrix d) ^ d = (-1 : ℂ) ^ (d - 1) • 1 := by
  have hdis : displacement d (1 : ZMod d) 1 = shiftMatrix d * clockMatrix d := by
    simp [displacement, ZMod.val_one'' (by omega : d ≠ 1)]
  rw [← hdis, D5.S3.Quantum.Algebra.WeylDisplacementPowers.displacement_pow]
  simp only [mul_one, ZMod.natCast_self, displacement_zero]
  rw [ZMod.val_natCast, D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod,
    Nat.choose_two_right, mul_comm d (d - 1), root_triangular]

private def peritoU (d : ℕ) [NeZero d] (y : Fin d) : Matrix (ZMod d) (ZMod d) ℂ :=
  (-windowRoot d ^ (1 - (y.val : ℤ))) • (shiftMatrix d * clockMatrix d)

private theorem peritoU_pow (d : ℕ) [NeZero d] (hd : 2 ≤ d) (y : Fin d) :
    peritoU d y ^ d = -1 := by
  have ha : (-windowRoot d ^ (1 - (y.val : ℤ))) ^ d = (-1 : ℂ) ^ d := by
    rw [neg_pow]
    have hh : (windowRoot d ^ (1 - (y.val : ℤ))) ^ d = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        (windowRoot_isPrimitiveRoot d).pow_eq_one, one_zpow]
    rw [hh, mul_one]
  rw [peritoU, smul_pow, ha, shift_clock_pow d hd, smul_smul, ← pow_add]
  rw [show d + (d - 1) = 2 * (d - 1) + 1 by omega]
  simp [pow_add, pow_mul]

private def gPolynomial (d : ℕ) : Polynomial ℂ :=
  ∑ k : Fin d, Polynomial.C
    (1 / ((d : ℂ) * (Real.sin (Real.pi / d * ((k.val : ℝ) + 1 / 2)) : ℂ))) *
      Polynomial.X ^ k.val

private theorem g_aeval {A : Type*} [Ring A] [Algebra ℂ A] (d : ℕ) (u : A) :
    Polynomial.aeval u (gPolynomial d) = ∑ k : Fin d,
      (1 / ((d : ℂ) * (Real.sin (Real.pi / d * ((k.val : ℝ) + 1 / 2)) : ℂ))) •
        u ^ k.val := by
  simp only [gPolynomial, map_sum, map_mul, map_pow, Polynomial.aeval_C,
    Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

private theorem g_eval (d : ℕ) (z : ℂ) :
    (gPolynomial d).eval z = peritoG d z := by
  simp only [gPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, peritoG]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem g_aeval_star {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    [StarModule ℂ A] (d : ℕ) (u : A) :
    Polynomial.aeval (star u) (gPolynomial d) = star (Polynomial.aeval u (gPolynomial d)) := by
  rw [g_aeval, g_aeval]
  simp only [star_sum, star_smul, star_pow]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  simp only [star_div₀, star_mul, star_one, star_natCast, Complex.star_def,
    Complex.conj_ofReal]
  ring

private theorem peritoU_unitary (d : ℕ) [NeZero d] (y : Fin d) :
    peritoU d y ∈ Matrix.unitaryGroup (ZMod d) ℂ := by
  have hnorm : ‖-windowRoot d ^ (1 - (y.val : ℤ))‖ = 1 := by
    rw [norm_neg, norm_zpow, (windowRoot_isPrimitiveRoot d).norm'_eq_one (NeZero.ne d),
      one_zpow]
  have ha : -windowRoot d ^ (1 - (y.val : ℤ)) ∈ unitary ℂ := by
    apply Unitary.mem_iff.mpr
    constructor
    · simpa [RCLike.star_def, hnorm] using
        RCLike.conj_mul (-windowRoot d ^ (1 - (y.val : ℤ)))
    · simpa [RCLike.star_def, hnorm] using
        RCLike.mul_conj (-windowRoot d ^ (1 - (y.val : ℤ)))
  apply Unitary.smul_mem_of_mem ha
  exact (Matrix.unitaryGroup (ZMod d) ℂ).mul_mem
    (Matrix.mem_unitaryGroup_iff'.mpr (window_unitary (M := d)).1)
    (Matrix.mem_unitaryGroup_iff'.mpr (window_unitary (M := d)).2)

private theorem unitary_star_from_pow {A : Type*} [Ring A] [StarRing A]
    (d : ℕ) (hd : 0 < d) (u : A) (hu : u ^ d = -1) (hs : star u * u = 1) :
    star u = -(u ^ (d - 1)) := by
  calc
    star u = -(star u * u ^ d) := by rw [hu]; simp
    _ = -(u ^ (d - 1)) := by
      rw [show d = (d - 1) + 1 by omega, pow_succ', ← mul_assoc, hs, one_mul]
      simp

private theorem g_matrix_unitary (d : ℕ) [NeZero d] (u : Matrix (ZMod d) (ZMod d) ℂ)
    (hu : u ^ d = -1) (hus : u ∈ Matrix.unitaryGroup (ZMod d) ℂ) :
    Polynomial.aeval u (gPolynomial d) ∈ Matrix.unitaryGroup (ZMod d) ℂ := by
  let q : Polynomial ℂ := (gPolynomial d).comp
    (Polynomial.C (-1) * Polynomial.X ^ (d - 1))
  have hstar : star u = -(u ^ (d - 1)) := unitary_star_from_pow d (NeZero.pos d) u hu
    (Matrix.mem_unitaryGroup_iff'.mp hus)
  have hq : Polynomial.aeval u q = star (Polynomial.aeval u (gPolynomial d)) := by
    dsimp [q]
    rw [Polynomial.aeval_comp]
    simp only [map_pow, Polynomial.aeval_X, map_neg, map_one, neg_one_mul, ← hstar]
    exact g_aeval_star d u
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [← hq, ← map_mul]
  have hh := matrix_polynomial_eq d u hu ((gPolynomial d) * q) 1 (by
    intro j
    have hnorm : ‖peritoNu d j‖ = 1 := by
      rw [peritoNu]
      convert Complex.norm_exp_ofReal_mul_I (Real.pi * (2 * j.val + 1) / d) using 1
      push_cast; congr 2; ring
    have hs : star (peritoNu d j) * peritoNu d j = 1 := by
      simpa [RCLike.star_def, hnorm] using RCLike.conj_mul (peritoNu d j)
    have hstarj := unitary_star_from_pow d (NeZero.pos d) (peritoNu d j)
      (peritoNu_pow d j) hs
    have hg : ‖(gPolynomial d).eval (peritoNu d j)‖ = 1 := by
      rw [g_eval, peritoG_at_nu]
      convert Complex.norm_exp_ofReal_mul_I
        (Real.pi / (2 * d) * ((d : ℝ) - 1 - 2 * j.val)) using 1
      push_cast; rfl
    rw [Polynomial.eval_mul, Polynomial.eval_one]
    have hqj : q.eval (peritoNu d j) = star ((gPolynomial d).eval (peritoNu d j)) := by
      dsimp [q]
      rw [Polynomial.eval_comp]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, neg_one_mul, ← hstarj]
      convert g_aeval_star d (peritoNu d j) using 1 <;> rfl
    rw [hqj]
    simpa [RCLike.star_def, hg] using RCLike.mul_conj ((gPolynomial d).eval (peritoNu d j)))
  simpa using hh

private theorem peritoU_power_term (d : ℕ) [NeZero d] (hd : 2 ≤ d) (y k : Fin d) :
    peritoU d y ^ k.val =
      ((-1 : ℂ) ^ k.val * windowRoot d ^ k.val.choose 2 *
        windowRoot d ^ ((1 - (y.val : ℤ)) * (k.val : ℤ))) •
          (shiftMatrix d ^ k.val * clockMatrix d ^ k.val) := by
  have hdis : displacement d (1 : ZMod d) 1 = shiftMatrix d * clockMatrix d := by
    simp [displacement, ZMod.val_one'' (by omega : d ≠ 1)]
  rw [peritoU, smul_pow, ← hdis,
    D5.S3.Quantum.Algebra.WeylDisplacementPowers.displacement_pow]
  simp only [mul_one, displacement, ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt]
  rw [D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_mod, smul_smul, neg_pow]
  rw [← zpow_natCast (windowRoot d ^ (1 - (y.val : ℤ))) k.val, ← zpow_mul]
  congr 1
  ring

private theorem coefficient_factor (d : ℕ) [NeZero d] (y k : Fin d) :
    windowRoot d ^ (-(y.val : ℤ)) *
      (1 / ((d : ℂ) * (Real.sin (Real.pi / d * ((k.val : ℝ) + 1 / 2)) : ℂ))) *
      ((-1 : ℂ) ^ k.val * windowRoot d ^ k.val.choose 2 *
        windowRoot d ^ ((1 - (y.val : ℤ)) * (k.val : ℤ))) = peritoLambda d y k := by
  have hroot : windowRoot d ≠ 0 := (windowRoot_isPrimitiveRoot d).ne_zero (NeZero.ne d)
  have htri : k.val * (k.val + 1) / 2 = k.val.choose 2 + k.val := by
    calc
      k.val * (k.val + 1) / 2 = (k.val + 1).choose 2 := by
        rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]
      _ = k.val.choose 2 + k.val := by
        rw [Nat.choose_succ_succ' k.val 1, Nat.choose_one_right, add_comm]
  have he : windowRoot d ^ (-(y.val : ℤ)) * windowRoot d ^ k.val.choose 2 *
      windowRoot d ^ ((1 - (y.val : ℤ)) * (k.val : ℤ)) =
        windowRoot d ^ (k.val * (k.val + 1) / 2) *
          windowRoot d ^ (-(y.val * (1 + k.val) : ℤ)) := by
    simp only [← zpow_natCast (windowRoot d) (k.val.choose 2),
      ← zpow_natCast (windowRoot d) (k.val * (k.val + 1) / 2)]
    rw [← zpow_add₀ hroot, ← zpow_add₀ hroot, ← zpow_add₀ hroot]
    congr 1
    rw [htri]
    push_cast
    ring
  rw [peritoLambda]
  calc
    _ = (-1 : ℂ) ^ k.val *
        (windowRoot d ^ (-(y.val : ℤ)) * windowRoot d ^ k.val.choose 2 *
          windowRoot d ^ ((1 - (y.val : ℤ)) * (k.val : ℤ))) /
        ((d : ℂ) * (Real.sin (Real.pi / d * ((k.val : ℝ) + 1 / 2)) : ℂ)) := by ring
    _ = _ := by rw [he]; ring

private theorem peritoB_factor (d : ℕ) [NeZero d] (hd : 2 ≤ d) (y : Fin d) :
    peritoB d y = windowRoot d ^ (-(y.val : ℤ)) •
      (shiftMatrix d * Polynomial.aeval (peritoU d y) (gPolynomial d)) := by
  rw [peritoB, g_aeval, Matrix.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hx : shiftMatrix d * (shiftMatrix d ^ k.val * clockMatrix d ^ k.val) =
      shiftMatrix d ^ (k.val + 1) * clockMatrix d ^ k.val := by
    rw [← mul_assoc, ← pow_succ']
  rw [Matrix.mul_smul, peritoU_power_term d hd, smul_smul,
    Matrix.mul_smul, smul_smul, hx]
  congr 1
  simpa only [mul_assoc] using (coefficient_factor d y k).symm

/-- Bob's cyclic matrices are unitary in every outcome dimension at least two. -/
theorem peritoB_unitary (d : ℕ) [NeZero d] (hd : 2 ≤ d) (y : Fin d) :
    peritoB d y ∈ Matrix.unitaryGroup (ZMod d) ℂ := by
  rw [peritoB_factor d hd]
  have hnorm : ‖windowRoot d ^ (-(y.val : ℤ))‖ = 1 := by
    rw [norm_zpow, (windowRoot_isPrimitiveRoot d).norm'_eq_one (NeZero.ne d), one_zpow]
  have ha : windowRoot d ^ (-(y.val : ℤ)) ∈ unitary ℂ := by
    constructor
    · simpa only [RCLike.star_def, hnorm, map_one, one_pow] using
        RCLike.conj_mul (windowRoot d ^ (-(y.val : ℤ)))
    · simpa only [RCLike.star_def, hnorm, map_one, one_pow] using
        RCLike.mul_conj (windowRoot d ^ (-(y.val : ℤ)))
  apply Unitary.smul_mem_of_mem ha
  exact (Matrix.unitaryGroup (ZMod d) ℂ).mul_mem
    (Matrix.mem_unitaryGroup_iff'.mpr (window_unitary (M := d)).1)
    (g_matrix_unitary d _ (peritoU_pow d hd y) (peritoU_unitary d y))

private theorem phase_product (d : ℕ) [NeZero d] :
    (∏ j : ZMod d, fourierPhase d j) = 1 := by
  have hdp : 0 < d := NeZero.pos d
  have hnat : (∑ j : ZMod d, j.val) * 2 = d * (d - 1) := by
    rw [← (ZMod.finEquiv d).toEquiv.sum_comp (fun j : ZMod d => j.val)]
    have hsum : (∑ j : Fin d, ((ZMod.finEquiv d).toEquiv j).val) =
        ∑ j : Fin d, j.val := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [fin_val]
    rw [hsum]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => j)]
    exact Finset.sum_range_id_mul_two d
  have hsum : (∑ j : ZMod d, (j.val : ℂ)) * 2 = (d : ℂ) * ((d : ℂ) - 1) := by
    have hh : ((d - 1 : ℕ) : ℂ) = (d : ℂ) - 1 := by
      have he : ((d - 1 : ℕ) : ℂ) + 1 = (d : ℂ) := by
        exact_mod_cast (Nat.sub_add_cancel hdp)
      linear_combination he
    have he : (∑ j : ZMod d, (j.val : ℂ)) * 2 = (d : ℂ) * ((d - 1 : ℕ) : ℂ) := by
      exact_mod_cast hnat
    simpa [hh] using he
  simp_rw [phase_centered]
  rw [← Complex.exp_sum]
  have hzero : (∑ j : ZMod d, ((Real.pi : ℂ) / (2 * d)) *
      ((d : ℂ) - 1 - 2 * j.val) * Complex.I) = 0 := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    linear_combination -((Real.pi : ℂ) / (2 * d)) * Complex.I * hsum
  rw [hzero, Complex.exp_zero]

private theorem peritoNu_add (d : ℕ) [NeZero d] (i j : ZMod d) :
    windowRoot d ^ i.val * peritoNu d j = peritoNu d (i + j) := by
  rw [peritoNu_factor, peritoNu_factor,
    D5.S3.Quantum.Algebra.WeylPhaseArithmetic.windowRoot_pow_val_add]
  ring

private def orbitPolynomial (d n : ℕ) : Polynomial ℂ :=
  ∏ j ∈ Finset.range n,
    (gPolynomial d).comp (Polynomial.C (windowRoot d ^ j) * Polynomial.X)

private theorem orbit_eval (d n : ℕ) (z : ℂ) :
    (orbitPolynomial d n).eval z =
      ∏ j ∈ Finset.range n, (gPolynomial d).eval (windowRoot d ^ j * z) := by
  simp only [orbitPolynomial, Polynomial.eval_prod, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

private theorem orbit_eval_root (d : ℕ) [NeZero d] (j : ZMod d) :
    (orbitPolynomial d d).eval (peritoNu d j) = 1 := by
  rw [orbit_eval]
  calc
    (∏ i ∈ Finset.range d, (gPolynomial d).eval (windowRoot d ^ i * peritoNu d j)) =
        ∏ i : ZMod d, fourierPhase d (i + j) := by
      rw [← Fin.prod_univ_eq_prod_range]
      refine Fintype.prod_equiv (ZMod.finEquiv d).toEquiv _ _ ?_
      intro i
      rw [g_eval]
      rw [show windowRoot d ^ i.val * peritoNu d j =
        peritoNu d ((ZMod.finEquiv d).toEquiv i + j) by
          rw [← fin_val d i]; exact peritoNu_add d _ j]
      exact peritoG_peritoNu d _
    _ = ∏ i : ZMod d, fourierPhase d i := by
      simpa using Equiv.prod_comp (Equiv.addRight j) (fourierPhase d)
    _ = 1 := phase_product d

private theorem peritoU_slide (d : ℕ) [NeZero d] (y : Fin d) :
    peritoU d y * shiftMatrix d =
      shiftMatrix d * (windowRoot d • peritoU d y) := by
  simp only [peritoU, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_assoc, window_weyl, Matrix.mul_smul, smul_smul]
  congr 1
  ring

private theorem peritoU_power_slide (d : ℕ) [NeZero d] (y : Fin d) (n : ℕ) :
    peritoU d y ^ n * shiftMatrix d =
      shiftMatrix d * (windowRoot d • peritoU d y) ^ n := by
  exact (SemiconjBy.pow_right (peritoU_slide d y).symm n).symm

private theorem polynomial_slide (d : ℕ) [NeZero d] (y : Fin d) (p : Polynomial ℂ) :
    Polynomial.aeval (peritoU d y) p * shiftMatrix d =
      shiftMatrix d * Polynomial.aeval (windowRoot d • peritoU d y) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, add_mul, mul_add, hp, hq]
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
    conv_lhs => arg 1; rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    conv_rhs => arg 2; rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [Matrix.smul_mul, peritoU_power_slide, Matrix.mul_smul]

private theorem orbit_matrix (d : ℕ) [NeZero d] (y : Fin d) (n : ℕ) :
    (shiftMatrix d * Polynomial.aeval (peritoU d y) (gPolynomial d)) ^ n =
      shiftMatrix d ^ n * Polynomial.aeval (peritoU d y) (orbitPolynomial d n) := by
  induction n with
  | zero =>
    rw [orbitPolynomial, Finset.range_zero, Finset.prod_empty,
      pow_zero, pow_zero, map_one, mul_one]
  | succ n ih =>
    have hstep : orbitPolynomial d (n + 1) = (orbitPolynomial d n).comp
        (Polynomial.C (windowRoot d) * Polynomial.X) * gPolynomial d := by
      unfold orbitPolynomial
      rw [Finset.prod_range_succ', Polynomial.prod_comp]
      simp only [pow_zero, Polynomial.C_1, one_mul, Polynomial.comp_X]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.X_comp, ← mul_assoc, ← Polynomial.C_mul, pow_succ]
    rw [pow_succ, ih, hstep, map_mul, Polynomial.aeval_comp]
    rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [← mul_assoc (shiftMatrix d ^ n * _),
      mul_assoc (shiftMatrix d ^ n), polynomial_slide, ← mul_assoc]
    rw [← pow_succ]
    rw [mul_assoc]

/-- Bob's cyclic observable has d-th power equal to the identity. -/
theorem peritoB_pow (d : ℕ) [NeZero d] (hd : 2 ≤ d) (y : Fin d) :
    peritoB d y ^ d = 1 := by
  have horbit : Polynomial.aeval (peritoU d y) (orbitPolynomial d d) = 1 := by
    have hh := matrix_polynomial_eq d (peritoU d y) (peritoU_pow d hd y)
      (orbitPolynomial d d) 1 (by intro j; simpa using orbit_eval_root d j)
    rw [map_one] at hh
    exact hh
  have hphase : (windowRoot d ^ (-(y.val : ℤ))) ^ d = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      (windowRoot_isPrimitiveRoot d).pow_eq_one, one_zpow]
  rw [peritoB_factor d hd, smul_pow, hphase, one_smul,
    orbit_matrix, shiftMatrix_pow_card, horbit, one_mul]

/-- Validity and the attained trace sum of the cyclic Bob strategy. -/
theorem peritoB_spec (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ y : Fin d, peritoB d y ∈ Matrix.unitaryGroup (ZMod d) ℂ ∧ peritoB d y ^ d = 1) ∧
    (∑ y : Fin d, (Matrix.trace ((clockMatrix d)ᵀ * peritoB d y) +
      windowRoot d ^ y.val * Matrix.trace ((shiftMatrix d)ᵀ * peritoB d y))) =
        (d : ℂ) * ((2 / Real.sin (Real.pi / (2 * (d : ℝ))) : ℝ) : ℂ) := by
  exact ⟨fun y => ⟨peritoB_unitary d hd y, peritoB_pow d hd y⟩, peritoB_attained_sum d hd⟩


/-- A unitary observable whose eigenvalues are `d`-th roots of unity. -/
def IsDObservable (d : ℕ) {a : Type*} [Fintype a] [DecidableEq a]
    (A : Matrix a a ℂ) : Prop :=
  A ∈ Matrix.unitaryGroup a ℂ ∧ A ^ d = 1

/-- The un-Hermitianized Bell operator; the Bell value takes its real expectation. -/
def bellOperator (d : ℕ) {a b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : Fin 2 → Matrix a a ℂ) (B : Fin d → Matrix b b ℂ) :
    Matrix (a × b) (a × b) ℂ :=
  ∑ x, ∑ y, windowRoot d ^ (x.val * y.val) • (A x ⊗ₖ B y)

/-- Real trace expectation, equal to the expectation of the Hermitian part. -/
def bellValue (d : ℕ) {a b : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (A : Fin 2 → Matrix a a ℂ) (B : Fin d → Matrix b b ℂ)
    (ρ : Matrix (a × b) (a × b) ℂ) : ℝ :=
  (Matrix.trace (ρ * bellOperator d A B)).re

/-- Amplitudes of the normalized maximally entangled vector in a finite basis. -/
def maxEntangledVector (ι : Type*) [Fintype ι] [DecidableEq ι] (i : ι × ι) : ℂ :=
  if i.1 = i.2 then ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) else 0

/-- The rank-one matrix of the maximally entangled vector. -/
def maxEntangled (ι : Type*) [Fintype ι] [DecidableEq ι] : Matrix (ι × ι) (ι × ι) ℂ :=
  Matrix.vecMulVec (maxEntangledVector ι) (star (maxEntangledVector ι))

/-- The bound for every finite projective strategy, and validity and attainment
of the explicit cyclic strategy. Density hypotheses use the canonical carrier. -/
def claim : Prop := ∀ (d : ℕ) (hd : 2 ≤ d),
  letI : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  (∀ (n m : ℕ) (A : Fin 2 → Matrix (Fin n) (Fin n) ℂ)
      (B : Fin d → Matrix (Fin m) (Fin m) ℂ) (ρ : DensityState (Fin n × Fin m)),
    (∀ x, IsDObservable d (A x)) → (∀ y, IsDObservable d (B y)) →
      bellValue d A B ρ.1 ≤ 2 / Real.sin (Real.pi / (2 * (d : ℝ)))) ∧
  (∀ x, IsDObservable d ((![clockMatrix d, shiftMatrix d]) x)) ∧
  (∀ y, IsDObservable d (peritoB d y)) ∧
  (0 ≤ CStarMatrix.ofMatrix (maxEntangled (ZMod d)) ∧
    Matrix.trace (maxEntangled (ZMod d)) = 1) ∧
  bellValue d ![clockMatrix d, shiftMatrix d] (peritoB d) (maxEntangled (ZMod d)) =
    2 / Real.sin (Real.pi / (2 * (d : ℝ)))

open Matrix

/-- A positive trace-one matrix bounds every real trace expectation by the operator norm. -/
private theorem density_trace_re_le_norm {a : Type*} [Fintype a] [DecidableEq a]
    (ρ : DensityState a) (M : Matrix a a ℂ) :
    (trace (CStarMatrix.ofMatrix.symm ρ.1 * M)).re ≤ ‖M‖ := by
  let R : Matrix a a ℂ := CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.1
  have hR : R.PosSemidef := (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1).posSemidef
  have htr : trace R = 1 := ρ.2.2
  let H : Matrix a a ℂ := (1 / 2 : ℝ) • (M + star M)
  have hH : IsSelfAdjoint H := by
    change star H = H
    simp [H, star_smul, add_comm]
  have hn : ‖H‖ ≤ ‖M‖ := by
    calc
      ‖H‖ = (1 / 2 : ℝ) * ‖M + star M‖ := by rw [norm_smul]; norm_num
      _ ≤ (1 / 2 : ℝ) * (‖M‖ + ‖star M‖) := by gcongr; exact norm_add_le _ _
      _ = ‖M‖ := by rw [norm_star]; ring
  have hp : ((‖H‖ : ℝ) • (1 : Matrix a a ℂ) - H).PosSemidef := by
    have ho := hH.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at ho
    exact ho
  have ht := RHLinalg.trace_mul_nonneg_of_posSemidef hR hp
  have hc : trace (R * star M) = star (trace (R * M)) := by
    rw [← trace_conjTranspose, conjTranspose_mul, hR.isHermitian.eq, trace_mul_comm]
    rfl
  have he : (trace (R * H)).re = (trace (R * M)).re := by
    simp only [H, mul_smul_comm, mul_add, trace_smul, trace_add, hc]
    simp only [Complex.real_smul]; norm_num; ring
  have ht' : (trace (R * H)).re ≤ ‖H‖ := by
    simp only [mul_sub, trace_sub, mul_smul_comm, mul_one, trace_smul, htr] at ht
    simpa [RCLike.re, Complex.real_smul] using ht
  exact (he ▸ ht').trans hn

/-- Factoring Alice's first unitary leaves the relative unitary in the tensor sum. -/
private theorem bell_operator_factor {a b : Type*} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (d : ℕ)
    (A : Fin 2 → Matrix a a ℂ) (B : Fin d → Matrix b b ℂ)
    (hA : A 0 ∈ unitaryGroup a ℂ) :
    bellOperator d A B = (A 0 ⊗ₖ (1 : Matrix b b ℂ)) *
      ∑ y, (1 + windowRoot d ^ y.val • (star (A 0) * A 1)) ⊗ₖ B y := by
  simp only [bellOperator, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    zero_mul, one_mul, pow_zero, one_smul]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← mul_kronecker_mul, one_mul, mul_add, mul_one, mul_smul_comm,
    ← mul_assoc, Unitary.mul_star_self_of_mem hA, one_mul, add_kronecker, smul_kronecker]

/-- Every finite unitary strategy satisfies the Perito Bell upper bound. -/
theorem bell_value_le {n m : ℕ} (d : ℕ) (hd : 2 ≤ d)
    (A : Fin 2 → Matrix (Fin n) (Fin n) ℂ)
    (B : Fin d → Matrix (Fin m) (Fin m) ℂ) (ρ : DensityState (Fin n × Fin m))
    (hA : ∀ x, A x ∈ unitaryGroup (Fin n) ℂ)
    (hB : ∀ y, B y ∈ unitaryGroup (Fin m) ℂ) :
    bellValue d A B ρ.1 ≤ 2 / Real.sin (Real.pi / (2 * (d : ℝ))) := by
  apply (density_trace_re_le_norm ρ (bellOperator d A B)).trans
  rw [bell_operator_factor d A B (hA 0), CStarRing.norm_mem_unitary_mul _
    (kronecker_mem_unitary (hA 0) (unitaryGroup (Fin m) ℂ).one_mem)]
  exact D5.S3.QuantumBounds.PeritoTensorBlockBound.tensor_block_bound _ B
    ((unitaryGroup (Fin n) ℂ).mul_mem (Unitary.star_mem (hA 0)) (hA 1)) hB _
    (D5.S3.QuantumBounds.PeritoUnitCircleSum.unit_circle_sum_le d hd)

/-- The cyclic clock and shift are d-observables. -/
theorem clock_shift_observables (d : ℕ) [NeZero d] : ∀ x,
    IsDObservable d ((![clockMatrix d, shiftMatrix d]) x) := by
  intro x
  fin_cases x
  · exact ⟨mem_unitaryGroup_iff'.mpr window_unitary.2, clockMatrix_pow_card⟩
  · exact ⟨mem_unitaryGroup_iff'.mpr window_unitary.1, shiftMatrix_pow_card⟩

/-- The maximally entangled rank-one matrix is a density matrix. -/
theorem max_entangled_density (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    0 ≤ CStarMatrix.ofMatrix (maxEntangled ι) ∧ trace (maxEntangled ι) = 1 := by
  constructor
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (posSemidef_vecMulVec_self_star (maxEntangledVector ι)).nonneg
  · have hs : (Real.sqrt (Fintype.card ι : ℝ) : ℂ) ^ 2 = (Fintype.card ι : ℂ) := by
      exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι))
    unfold maxEntangled maxEntangledVector
    simp only [trace, diag, vecMulVec,
      Pi.star_apply, RCLike.star_def, ite_mul, zero_mul, of_apply,
      Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Complex.ofReal_inv, map_inv₀, Complex.conj_ofReal, ← sq, inv_pow, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hs0 : (Real.sqrt (Fintype.card ι : ℝ) : ℂ) ≠ 0 := by
      intro hz
      have hd : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      exact hd (by simpa [hz] using hs.symm)
    rw [← hs]
    exact mul_inv_cancel₀ (pow_ne_zero 2 hs0)

/-- The maximally entangled expectation contracts a tensor product by ordinary transpose. -/
theorem max_entangled_trace (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Matrix ι ι ℂ) :
    trace (maxEntangled ι * (A ⊗ₖ B)) = trace (Aᵀ * B) / (Fintype.card ι : ℂ) := by
  unfold maxEntangled maxEntangledVector
  simp only [trace, diag, mul_apply, vecMulVec_apply,
    Pi.star_apply, RCLike.star_def, kronecker_apply, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, mul_zero, apply_ite, map_zero,
    Complex.ofReal_inv, map_inv₀, Complex.conj_ofReal, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, transpose_apply]
  have hs : (Real.sqrt (Fintype.card ι : ℝ) : ℂ) ^ 2 = (Fintype.card ι : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι))
  have hc : (Real.sqrt (Fintype.card ι : ℝ) : ℂ)⁻¹ *
      (Real.sqrt (Fintype.card ι : ℝ) : ℂ)⁻¹ = (Fintype.card ι : ℂ)⁻¹ := by
    rw [← mul_inv, ← sq, hs]
  simp only [hc, ← Finset.mul_sum, div_eq_mul_inv]
  exact mul_comm _ _

/-- The Perito Bell bound and its explicit cyclic strategy. -/
theorem result : claim := by
  intro d hd
  let : NeZero d := ⟨Nat.ne_zero_of_lt hd⟩
  have bob_observables : ∀ y, IsDObservable d (peritoB d y) :=
    (peritoB_spec d hd).1
  have attained_value :
      bellValue d ![clockMatrix d, shiftMatrix d] (peritoB d) (maxEntangled (ZMod d)) =
        2 / Real.sin (Real.pi / (2 * (d : ℝ))) := by
    have he (B : Fin d → Matrix (ZMod d) (ZMod d) ℂ) :
        trace (maxEntangled (ZMod d) * bellOperator d ![clockMatrix d, shiftMatrix d] B) =
        (∑ y : Fin d, (trace ((clockMatrix d)ᵀ * B y) +
          windowRoot d ^ y.val * trace ((shiftMatrix d)ᵀ * B y))) / (d : ℂ) := by
      have hbell : bellOperator d ![clockMatrix d, shiftMatrix d] B =
          (∑ y : Fin d, clockMatrix d ⊗ₖ B y) +
            ∑ y : Fin d, windowRoot d ^ y.val • (shiftMatrix d ⊗ₖ B y) := by
        simp only [bellOperator, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
          zero_mul, one_mul, pow_zero, one_smul, Matrix.cons_val_zero, Matrix.cons_val_one]
      calc
        _ = ∑ y : Fin d, (trace ((clockMatrix d)ᵀ * B y) / (d : ℂ) +
            windowRoot d ^ y.val * (trace ((shiftMatrix d)ᵀ * B y) / (d : ℂ))) := by
          rw [hbell, mul_add, Finset.mul_sum, Finset.mul_sum, trace_add,
            trace_sum, trace_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro y hy
          rw [max_entangled_trace, ZMod.card, mul_smul_comm, trace_smul,
            max_entangled_trace, ZMod.card]
          rfl
        _ = _ := by simp only [← mul_div_assoc, ← add_div, ← Finset.sum_div]
    rw [bellValue, he, peritoB_attained_sum d hd]
    have hdn : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
    rw [mul_div_cancel_left₀ _ hdn, Complex.ofReal_re]
  exact ⟨fun n m A B ρ hA hB => bell_value_le d hd A B ρ
      (fun x => (hA x).1) (fun y => (hB y).1),
    clock_shift_observables d, bob_observables, max_entangled_density (ZMod d), attained_value⟩

#print axioms result

end D5.S3.QuantumBounds.PeritoTsirelson

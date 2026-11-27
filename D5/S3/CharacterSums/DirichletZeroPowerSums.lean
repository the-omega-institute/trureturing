/- GID: D5/S3/CharacterSums/DirichletZeroPowerSums
   generality: G
   mirror-B: D5/B/S3/CharacterSums/DirichletZeroPowerSums
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Dirichlet moments equal the absolutely convergent zero power sums. -/

import D5.S3.CharacterSums.DirichletTrivialZeros
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds
import D5.S3.Analytic.Resolvent.EntireLogDerivPowers

/-! # Actual zero power sums for Dirichlet L-functions

The original L-function has subquadratic power growth, including at its trivial zeros.
Its logarithmic derivatives therefore recover all zeros with analytic multiplicity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter Set Topology MeasureTheory
namespace D5.S3.CharacterSums.DirichletZeroPowerSums
open D5.S3.CharacterSums.DirichletTrivialZeros
open D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds

def momentTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (k : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  (k.factorial : ℂ)⁻¹ * LSeries.term
    (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * (Real.log n : ℂ) ^ k)
    (2 + t * I) n

def moment {q : ℕ} (χ : DirichletCharacter ℂ q) (k : ℕ) (t : ℝ) : ℝ :=
  -(∑' n, momentTerm χ k t n).re

def finiteMoment {q : ℕ} (χ : DirichletCharacter ℂ q) (k X : ℕ) (t : ℝ) : ℝ :=
  -(∑ n ∈ Finset.range (X + 1), momentTerm χ k t n).re

private def majorantConstant (k : ℕ) : ℝ := 2 ^ (k + 1) * (k + 1)

private theorem log_power_majorant (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ (k + 1) / (k.factorial : ℝ) ≤
      majorantConstant k * x ^ (1 / 2 : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hf : (0 : ℝ) < k.factorial := by positivity
  have h := Real.pow_div_factorial_le_exp (Real.log x / 2) (div_nonneg hl (by norm_num)) (k + 1)
  rw [show Real.exp (Real.log x / 2) = x ^ (1 / 2 : ℝ) by
    rw [Real.rpow_def_of_pos hx0]; congr 1; ring] at h
  have he : (Real.log x / 2) ^ (k + 1) / ((k + 1).factorial : ℝ) *
      majorantConstant k = Real.log x ^ (k + 1) / (k.factorial : ℝ) := by
    rw [div_pow, Nat.factorial_succ]
    push_cast
    dsimp [majorantConstant]
    field_simp
    <;> ring
  rw [← he]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right h
    (show 0 ≤ majorantConstant k by dsimp [majorantConstant]; positivity)

private theorem norm_term_majorant {q : ℕ} (χ : DirichletCharacter ℂ q)
    (k : ℕ) (t : ℝ) (n : ℕ) :
    ‖momentTerm χ k t n‖ ≤ majorantConstant k * (n : ℝ) ^ (-3 / 2 : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [momentTerm]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hχ : ‖χ n‖ * ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
    (mul_le_of_le_one_left hΛ (χ.norm_le_one _)).trans
      ArithmeticFunction.vonMangoldt_le_log
  have hp := log_power_majorant k hn1
  have he : (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 =
      (n : ℝ) ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_sub hn0]
    norm_num
  dsimp [momentTerm]
  rw [norm_mul, norm_inv, Complex.norm_natCast, LSeries.norm_term_eq, ite_eq_right hn]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hΛ, abs_of_nonneg hl, add_re, mul_re, ofReal_re,
    I_re, mul_zero, ofReal_im, I_im, zero_mul, sub_self, add_zero]
  norm_num only [show (2 : ℂ).re = 2 by norm_num, Real.rpow_two]
  calc
    _ ≤ (k.factorial : ℝ)⁻¹ * (Real.log n ^ (k + 1) / (n : ℝ) ^ 2) := by
      gcongr
      simpa [pow_succ, mul_comm] using mul_le_mul_of_nonneg_right hχ (pow_nonneg hl k)
    _ = (Real.log n ^ (k + 1) / (k.factorial : ℝ)) / (n : ℝ) ^ 2 := by ring
    _ ≤ (majorantConstant k * (n : ℝ) ^ (1 / 2 : ℝ)) / (n : ℝ) ^ 2 := by
      gcongr
    _ = _ := by rw [mul_div_assoc, he]; norm_num

private theorem term_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (k : ℕ) (t : ℝ) : Summable (momentTerm χ k t) := by
  exact ((Real.summable_nat_rpow.mpr (by norm_num : (-3 / 2 : ℝ) < -1)).mul_left
    (majorantConstant k)).of_norm_bounded (norm_term_majorant χ k t)

private theorem rpow_tail (X : ℕ) (hX : 0 < X) :
    (∑' n : ℕ, ((n + X + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) ≤
      2 * (X : ℝ) ^ (-1 / 2 : ℝ) := by
  have hp : (0 : ℝ) < X := by exact_mod_cast hX
  have ha : AntitoneOn (fun x : ℝ => x ^ (-3 / 2 : ℝ)) (Ici (X : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hp.trans_le hx) hxy (by norm_num)
  have h := ha.tsum_comp_add_le_integral X
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hp)
    (fun x hx => Real.rpow_nonneg (hp.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) hp] at h
  convert h using 1 <;> norm_num [Nat.cast_add] <;> ring

private theorem tail_norm {q : ℕ} (χ : DirichletCharacter ℂ q)
    (k X : ℕ) (t : ℝ) (hX : 0 < X) :
    ‖(∑' n, momentTerm χ k t n) -
      ∑ n ∈ Finset.range (X + 1), momentTerm χ k t n‖ ≤
      majorantConstant k * (2 * (X : ℝ) ^ (-1 / 2 : ℝ)) := by
  have hs := term_summable χ k t
  have hst : Summable (fun n : ℕ => momentTerm χ k t (n + (X + 1))) :=
    (summable_nat_add_iff (X + 1)).mpr hs
  have hmt : Summable (fun n : ℕ => ((n + X + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (X + 1)).mpr
        (Real.summable_nat_rpow.mpr (by norm_num : (-3 / 2 : ℝ) < -1))
  rw [← hs.sum_add_tsum_nat_add (X + 1), add_sub_cancel_left]
  calc
    _ ≤ ∑' n : ℕ, ‖momentTerm χ k t (n + (X + 1))‖ :=
      norm_tsum_le_tsum_norm hst.norm
    _ ≤ ∑' n : ℕ, majorantConstant k *
        (((n + X + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) := by
      apply Summable.tsum_le_tsum
      · intro n
        simpa [Nat.add_assoc] using norm_term_majorant χ k t (n + (X + 1))
      · exact hst.norm
      · exact hmt.mul_left (majorantConstant k)
    _ = majorantConstant k *
        ∑' n : ℕ, (((n + X + 1 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_tail X hX)
      (by dsimp [majorantConstant]; positivity)

private theorem exponential_tail_bound (k : ℕ) :
    majorantConstant k * (2 * Real.exp (-2 * (k + 1 : ℝ))) ≤ (2 / 3 : ℝ) ^ (k + 1) := by
  have hk : k + 1 ≤ 2 ^ k := by have h : k < 2 ^ k := Nat.lt_two_pow_self; omega
  have he : (6 : ℝ) ≤ Real.exp 2 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) 4
    norm_num [Finset.sum_range_succ] at h
    linarith
  have he' : Real.exp (-2) ≤ 1 / 6 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (inv_le_inv₀ (Real.exp_pos 2) (by norm_num : (0 : ℝ) < 6)).mpr he
  have hexp : Real.exp (-2 * (k + 1 : ℝ)) = Real.exp (-2) ^ (k + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  calc
    _ ≤ (4 : ℝ) ^ (k + 1) * Real.exp (-2) ^ (k + 1) := by
      have hk' : (k + 1 : ℝ) ≤ 2 ^ k := by exact_mod_cast hk
      have hpow : (4 : ℝ) ^ (k + 1) = 2 ^ (k + 1) * (2 ^ k * 2) := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_succ (2 : ℝ) k]
      dsimp [majorantConstant]
      rw [hpow]
      nlinarith [mul_le_mul_of_nonneg_left hk'
        (show 0 ≤ 2 ^ (k + 1) * (2 * Real.exp (-2) ^ (k + 1)) by positivity)]
    _ = (4 * Real.exp (-2)) ^ (k + 1) := by rw [mul_pow]
    _ ≤ (2 / 3 : ℝ) ^ (k + 1) := by
      gcongr
      linarith

/-- The arithmetic series converges without a cutoff condition. Every positive cutoff
has an explicit tail bound, and an exponential cutoff gives the sharper geometric error. -/
theorem finite_moment_error {q : ℕ} (χ : DirichletCharacter ℂ q)
    (k X : ℕ) (t : ℝ) :
    Summable (momentTerm χ k t) ∧
      (0 < X → ‖(∑' n, momentTerm χ k t n) -
        ∑ n ∈ Finset.range (X + 1), momentTerm χ k t n‖ ≤
          2 ^ (k + 2) * (k + 1) * (X : ℝ) ^ (-1 / 2 : ℝ)) ∧
      (Real.exp (4 * (k + 1 : ℝ)) ≤ (X : ℝ) →
        ‖(∑' n, momentTerm χ k t n) -
          ∑ n ∈ Finset.range (X + 1), momentTerm χ k t n‖ ≤ (2 / 3 : ℝ) ^ (k + 1) ∧
        |moment χ k t - finiteMoment χ k X t| ≤ (2 / 3 : ℝ) ^ (k + 1)) := by
  refine ⟨term_summable χ k t, ?_, ?_⟩
  · intro hX
    convert tail_norm χ k X t hX using 1
    dsimp [majorantConstant]
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  intro hX
  have hX0 : 0 < X := by exact_mod_cast (Real.exp_pos _).trans_le hX
  have hpow : (X : ℝ) ^ (-1 / 2 : ℝ) ≤ Real.exp (-2 * (k + 1 : ℝ)) := by
    calc
      _ ≤ (Real.exp (4 * (k + 1 : ℝ))) ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hX (by norm_num)
      _ = _ := by rw [← Real.exp_mul]; congr 1; ring
  have hr : |moment χ k t - finiteMoment χ k X t| ≤
      ‖(∑' n, momentTerm χ k t n) -
        ∑ n ∈ Finset.range (X + 1), momentTerm χ k t n‖ := by
    change |-(∑' n, momentTerm χ k t n).re -
      -(∑ n ∈ Finset.range (X + 1), momentTerm χ k t n).re| ≤ _
    rw [neg_sub_neg, abs_sub_comm, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  have hb := (tail_norm χ k X t hX0).trans
    ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by norm_num))
      (by dsimp [majorantConstant]; positivity)).trans (exponential_tail_bound k))
  exact ⟨hb, hr.trans hb⟩


private theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have he := congrArg norm (Complex.two_sin z)
  rw [norm_mul, Complex.norm_ofNat, norm_mul, Complex.norm_I, mul_one] at he
  have hb := norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))
  rw [Complex.norm_exp, Complex.norm_exp] at hb
  have hp : (z * I).re ≤ |z.im| := by
    simp only [mul_re, I_re, mul_zero, I_im, mul_one, zero_sub]
    exact neg_le_abs _
  have hm : (-z * I).re ≤ |z.im| := by
    simp only [neg_mul, neg_re, mul_re, I_re, mul_zero, I_im, mul_one, zero_sub, neg_neg]
    exact le_abs_self _
  linarith [Real.exp_le_exp.mpr hp, Real.exp_le_exp.mpr hm]

private theorem reciprocal_gamma_power_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖(Complex.Gamma z)⁻¹‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨x₀, hx₀, hmin⟩ := Real.exists_isMinOn_Gamma_Ioi
  let m := Real.Gamma x₀
  have hm : 0 < m := Real.Gamma_pos_of_pos (by linarith [hx₀.1])
  let A := max 1 (max m⁻¹ gammaConstant)
  let D := 2 * Real.log 2 + 4 + Real.pi
  have hA : 1 ≤ A := le_max_left _ _
  have hAp : 0 < A := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨Real.log A + D, add_nonneg (Real.log_nonneg hA) hD, fun z => ?_⟩
  let R := 1 + ‖z‖
  let H := R ^ (3 / 2 : ℝ)
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
  have hRp : 0 < R := by linarith
  have hroot : 1 ≤ R ^ (1 / 2 : ℝ) := Real.one_le_rpow hR (by norm_num)
  have hH : H = R * R ^ (1 / 2 : ℝ) := by
    dsimp [H]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hRp,
      Real.rpow_one]
  have hRH : R ≤ H := by rw [hH]; nlinarith
  have hH1 : 1 ≤ H := hR.trans hRH
  have hi : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans (by dsimp [R]; linarith)
  have hb : ‖(Complex.Gamma z)⁻¹‖ ≤ A * Real.exp (D * H) := by
    by_cases hz : 1 / 2 ≤ z.re
    · have hg : m ≤ Real.Gamma z.re := hmin (by change 0 < z.re; linarith)
      have hsq := norm_recip_Gamma_sq_le hz z.im
      have heq : (z.re : ℂ) + I * z.im = z := by apply Complex.ext <;> simp
      rw [heq] at hsq
      have he : Real.exp (Real.pi * |z.im|) =
          Real.exp (Real.pi * |z.im| / 2) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      have hsq' : ‖(Complex.Gamma z)⁻¹‖ ^ 2 ≤
          (m⁻¹ * Real.exp (Real.pi * |z.im| / 2)) ^ 2 := by
        apply hsq.trans
        calc
          _ ≤ Real.exp (Real.pi * |z.im| / 2) ^ 2 / m ^ 2 := by rw [he]; gcongr
          _ = _ := by rw [mul_pow, inv_pow]; ring
      have hnorm := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq'
      apply hnorm.trans
      apply mul_le_mul
      · exact (le_max_left m⁻¹ gammaConstant).trans (le_max_right 1 _)
      · apply Real.exp_le_exp.mpr
        have hl : 0 ≤ 2 * Real.log 2 + 4 := by positivity
        have hp := Real.pi_pos
        dsimp [D]
        nlinarith [mul_nonneg hl (by linarith : 0 ≤ H),
          mul_le_mul_of_nonneg_left (hi.trans hRH) hp.le]
      · positivity
      · exact hAp.le
    · have hu : 1 / 2 < (1 - z).re := by simp only [sub_re, one_re]; linarith
      have hlu : 0 ≤ Real.log ((1 - z).re + 1) :=
        Real.log_nonneg (by linarith)
      have hγ : 1 ≤ gammaConstant := le_max_left _ _
      have hG : Complex.Gamma (1 - z) ≠ 0 :=
        Complex.Gamma_ne_zero_of_re_pos (by linarith)
      have he : (Complex.Gamma z)⁻¹ =
          Complex.Gamma (1 - z) * Complex.sin (Real.pi * z) / Real.pi := by
        have hh := congrArg Inv.inv (Complex.Gamma_mul_Gamma_one_sub z)
        rw [mul_inv_rev, inv_div] at hh
        apply (eq_div_iff (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).mpr
        have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        field_simp [hG, hπ] at hh ⊢
        linear_combination hh
      have hΓ : ‖Complex.Gamma (1 - z)‖ ≤ gammaConstant *
          Real.exp (((1 - z).re + 1) * Real.log ((1 - z).re + 1)) := by
        apply (gamma_growth_bounds.1 (by linarith : 0 < (1 - z).re)).trans
        rcases gamma_growth_bounds.2.1 (by linarith : 1 / 4 ≤ (1 - z).re) with h | h
        · exact h.trans ((le_max_right _ _).trans
            (le_mul_of_one_le_right (zero_le_one.trans hγ)
              (Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hlu))))
        · exact h.le.trans (le_mul_of_one_le_left (Real.exp_pos _).le
            (le_max_left _ _))
      have hlR : Real.log R ≤ 2 * R ^ (1 / 2 : ℝ) := by
        have hh := Real.log_le_rpow_div hRp.le (by norm_num : (0 : ℝ) < 1 / 2)
        linarith
      have huR : (1 - z).re + 1 ≤ 2 * R := by
        simp only [sub_re, one_re]
        dsimp [R]
        linarith [neg_le_abs z.re, Complex.abs_re_le_norm z]
      have hlog : Real.log ((1 - z).re + 1) ≤ Real.log 2 + Real.log R := by
        rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hRp.ne']
        exact Real.log_le_log (by linarith) huR
      have hprod : ((1 - z).re + 1) * Real.log ((1 - z).re + 1) ≤
          2 * R * (Real.log 2 + 2 * R ^ (1 / 2 : ℝ)) := by
        apply mul_le_mul huR (hlog.trans (by linarith))
        · exact hlu
        · positivity
      have hsin : ‖Complex.sin (Real.pi * z)‖ ≤ Real.exp (Real.pi * |z.im|) := by
        simpa [abs_mul, abs_of_pos Real.pi_pos] using norm_sin_le_exp (Real.pi * z)
      rw [he, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      calc
        _ ≤ (gammaConstant *
            Real.exp (((1 - z).re + 1) * Real.log ((1 - z).re + 1))) *
              Real.exp (Real.pi * |z.im|) :=
          (div_le_self (by positivity) (by linarith [Real.pi_gt_three])).trans
            (mul_le_mul hΓ hsin (norm_nonneg _) (by positivity))
        _ = gammaConstant * Real.exp
            (((1 - z).re + 1) * Real.log ((1 - z).re + 1) + Real.pi * |z.im|) := by
          rw [Real.exp_add]; ring
        _ ≤ A * Real.exp (D * H) := by
          apply mul_le_mul
          · exact (le_max_right m⁻¹ gammaConstant).trans (le_max_right 1 _)
          · apply Real.exp_le_exp.mpr
            dsimp [D]
            rw [hH]
            have h₁ := mul_le_mul_of_nonneg_left hRH (by positivity : 0 ≤ Real.log 2)
            have h₂ := mul_le_mul_of_nonneg_left (hi.trans hRH) Real.pi_pos.le
            rw [hH] at h₁ h₂
            simp only [sub_re, one_re] at hprod
            nlinarith only [hprod, h₁, h₂]
          · positivity
          · exact hAp.le
  apply hb.trans
  rw [show A * Real.exp (D * H) = Real.exp (Real.log A + D * H) by
    rw [Real.exp_add, Real.exp_log hAp]]
  apply Real.exp_le_exp.mpr
  have hl : 0 ≤ Real.log A := Real.log_nonneg hA
  change Real.log A + D * H ≤ (Real.log A + D) * H
  nlinarith [mul_le_mul_of_nonneg_left hH1 hl]

private theorem reciprocal_gammaFactor_power_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      ‖(χ.gammaFactor s)⁻¹‖ ≤ Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  classical
  obtain ⟨C, hC, hbound⟩ := reciprocal_gamma_power_growth
  have hlπ : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨Real.log Real.pi / 2 + 4 * C, by positivity, fun s => ?_⟩
  let a : ℂ := if χ.Even then 0 else 1
  let w := s + a
  let R := 1 + ‖s‖
  let H := R ^ (3 / 2 : ℝ)
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg s]
  have hRp : 0 < R := by linarith
  have hRH : R ≤ H := by
    dsimp [H]
    simpa using Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have ha : ‖a‖ ≤ 1 := by dsimp [a]; split_ifs <;> norm_num
  have hw : ‖w‖ ≤ R := by dsimp [w, R]; linarith [norm_add_le s a]
  have hwre : w.re ≤ R := (Complex.re_le_norm w).trans hw
  have harg : 1 + ‖w / 2‖ ≤ 2 * R := by
    rw [norm_div, Complex.norm_ofNat]
    linarith
  have hpow : (1 + ‖w / 2‖) ^ (3 / 2 : ℝ) ≤ 4 * H := by
    calc
      _ ≤ (2 * R) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) harg (by norm_num)
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) * H := by
        rw [Real.mul_rpow (by norm_num) hRp.le]
      _ ≤ 4 * H := by
        apply mul_le_mul_of_nonneg_right _ (by dsimp [H]; positivity)
        calc
          (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 2 ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := by norm_num
  have heq : χ.gammaFactor s = Complex.Gammaℝ w := by
    unfold DirichletCharacter.gammaFactor
    dsimp [w, a]
    split_ifs <;> simp
  rw [heq, Complex.Gammaℝ_def, mul_inv_rev, norm_mul]
  simp only [norm_inv]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Real.rpow_def_of_pos Real.pi_pos, ← Real.exp_neg]
  simp only [neg_re, div_ofNat_re, mul_neg, neg_div, neg_neg]
  calc
    _ ≤ Real.exp (C * (1 + ‖w / 2‖) ^ (3 / 2 : ℝ)) *
        Real.exp (Real.log Real.pi * (w.re / 2)) :=
      mul_le_mul_of_nonneg_right (by simpa only [norm_inv] using hbound (w / 2))
        (Real.exp_pos _).le
    _ = Real.exp (C * (1 + ‖w / 2‖) ^ (3 / 2 : ℝ) +
        Real.log Real.pi * (w.re / 2)) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have h₁ := mul_le_mul_of_nonneg_left hpow hC
      have h₂ := mul_le_mul_of_nonneg_left (hwre.trans hRH) hlπ
      dsimp [H, R] at *
      nlinarith)

private theorem LFunction_power_growth {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    ∃ C : ℝ, ∀ s : ℂ,
      ‖χ.LFunction s‖ ≤ Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hGamma⟩ := reciprocal_gammaFactor_power_growth χ
  have hq : q ≠ 1 := by
    intro h
    subst q
    exact hne (Subsingleton.elim _ _)
  let b := Real.log (q : ℝ) / 2
  refine ⟨3 * growthConstant q + |b| + C, fun s => ?_⟩
  have he : χ.LFunction s =
      Complex.exp (-((b : ℝ) : ℂ) * s) * completion χ s * (χ.gammaFactor s)⁻¹ := by
    rw [χ.LFunction_eq_completed_div_gammaFactor s (.inr hq)]
    dsimp only [completion, b]
    rw [← mul_assoc, ← Complex.exp_add]
    simp only [neg_mul, neg_add_cancel, Complex.exp_zero, one_mul, div_eq_mul_inv]
  have hR : 1 ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hRH : ‖s‖ ≤ (1 + ‖s‖) ^ (3 / 2 : ℝ) := by
    apply (show ‖s‖ ≤ 1 + ‖s‖ by linarith).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hexp : ‖Complex.exp (-((b : ℝ) : ℂ) * s)‖ ≤
      Real.exp (|b| * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hh := (Complex.re_le_norm (-((b : ℝ) : ℂ) * s)).trans
      (by rw [norm_mul, norm_neg, Complex.norm_real])
    exact hh.trans (mul_le_mul_of_nonneg_left hRH (abs_nonneg b))
  rw [he, norm_mul, norm_mul]
  calc
    _ ≤ (Real.exp (|b| * (1 + ‖s‖) ^ (3 / 2 : ℝ)) *
        Real.exp (3 * growthConstant q * (1 + ‖s‖) ^ (3 / 2 : ℝ))) *
          Real.exp (C * (1 + ‖s‖) ^ (3 / 2 : ℝ)) :=
      mul_le_mul (mul_le_mul hexp (completion_power_growth hne s (.inr hχ)).2.2.le
        (norm_nonneg _) (Real.exp_pos _).le) (hGamma _) (norm_nonneg _)
          (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring


private theorem logDeriv_eq_neg_LSeries {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    logDeriv χ.LFunction s = -LSeries ((fun n : ℕ => χ n) *
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s := by
  rw [logDeriv_apply, χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs,
    χ.LSeries_twist_vonMangoldt_eq hs]
  ring

private theorem iterated_logMul {f : ℕ → ℂ} (k n : ℕ) :
    (LSeries.logMul^[k] f) n = (Real.log n : ℂ) ^ k * f n := by
  have he : LSeries.logMul =
      fun f : ℕ → ℂ => (fun n : ℕ => (Real.log n : ℂ)) * f := by
    funext f n
    simp [LSeries.logMul]
  rw [he]
  have h := congrFun (mul_left_iterate_apply
    (fun n : ℕ => (Real.log n : ℂ)) f (n := k)) n
  simpa only [Pi.mul_apply, Pi.pow_apply] using h


private theorem arithmetic_logDeriv_moment {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (logDeriv χ.LFunction) (2 + t * I) =
      -((-1 : ℂ) ^ k * (k.factorial : ℂ) * ∑' n, momentTerm χ k t n) := by
  let f : ℕ → ℂ := (fun n : ℕ => χ n) *
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
  have hs : (1 : ℝ) < (2 + t * I).re := by simp
  have he : logDeriv χ.LFunction =ᶠ[𝓝 (2 + t * I)] fun s => -LSeries f s := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with s hs
    exact logDeriv_eq_neg_LSeries χ hs
  have ha : LSeries.abscissaOfAbsConv f ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun x hx => χ.LSeriesSummable_twist_vonMangoldt (by simpa using hx))
  have hlt : LSeries.abscissaOfAbsConv f < (2 + t * I).re :=
    ha.trans_lt (by exact_mod_cast hs)
  rw [he.iteratedDeriv_eq k, iteratedDeriv_fun_neg, LSeries_iteratedDeriv k hlt]
  congr 1
  rw [mul_assoc]
  congr 1
  rw [← tsum_mul_left]
  unfold LSeries
  apply tsum_congr
  intro n
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [momentTerm, ← mul_assoc, mul_inv_cancel₀ hf, one_mul]
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs
  · rfl
  · rw [iterated_logMul]
    dsimp [f]
    ring


/-- Every positive-order arithmetic moment is the absolutely convergent inverse power
sum over all actual L-function zeros, with their analytic multiplicities. -/
theorem moment_zero_power_hasSum {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    HasSum (fun ρ : {z : ℂ // χ.LFunction z = 0} =>
      (analyticOrderNatAt χ.LFunction ρ.1 : ℂ) *
        (2 + t * I - ρ.1)⁻¹ ^ (k + 1)) (-(∑' n, momentTerm χ k t n)) ∧
    Summable (fun ρ : {z : ℂ // χ.LFunction z = 0} =>
      ‖(analyticOrderNatAt χ.LFunction ρ.1 : ℂ) *
        (2 + t * I - ρ.1)⁻¹ ^ (k + 1)‖) ∧
    moment χ k t = (∑' ρ : {z : ℂ // χ.LFunction z = 0},
      (analyticOrderNatAt χ.LFunction ρ.1 : ℂ) *
        (2 + t * I - ρ.1)⁻¹ ^ (k + 1)).re := by
  obtain ⟨C, hg⟩ := LFunction_power_growth hχ hne
  have hs := D5.S3.Analytic.Resolvent.EntireLogDerivPowers.entire_logDeriv_power_hasSum
    (χ.differentiable_LFunction hne) (by norm_num : (3 / 2 : ℝ) < 2)
    hg k hk (χ.LFunction_ne_zero_of_one_le_re
      (s := 2 + t * I) (.inl hne) (by simp))
  have hv : ((-1 : ℂ) ^ k / k.factorial) *
      iteratedDeriv k (logDeriv χ.LFunction) (2 + t * I) =
      -(∑' n, momentTerm χ k t n) := by
    rw [arithmetic_logDeriv_moment]
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hp : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; norm_num
    generalize (∑' n, momentTerm χ k t n) = S
    calc
      _ = -(((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * S) := by field_simp
      _ = -S := by rw [hp, one_mul]
  rw [hv] at hs
  refine ⟨hs, hs.summable.norm, ?_⟩
  rw [hs.tsum_eq]
  rfl

end D5.S3.CharacterSums.DirichletZeroPowerSums

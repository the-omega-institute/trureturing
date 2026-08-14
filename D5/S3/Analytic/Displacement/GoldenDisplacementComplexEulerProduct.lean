/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct
   generality: I
   mirror-B: D5/B/S3/Analytic/Displacement/GoldenDisplacementComplexEulerProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Lifts the displacement Euler product to complex parameters and identifies its convergent golden-conjugate germ section. -/

import D5.S1.Deficit.Displacement.GoldenDisplacementEulerProduct
import D5.S3.Analytic.GoldenEulerBeta

/- Provenance: the complex Euler product is the pinned mathlib
   `EulerProduct.eulerProduct_tprod` applied to the frozen displacement term;
   norm control uses `Complex.norm_cpow_eq_rpow_re_of_pos`, and the germ rewrite
   uses the repository's substitution-start Beatty formula. -/

open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Words
open D5.S1.Words.Powers
open D5.S3.Analytic.GoldenEulerBeta
open GoldenDesubstitutionLength
open GoldenDesubstitutionZeckendorf
open GoldenDisplacementEulerProduct
open GoldenSubstitutionOrbit

namespace GoldenDisplacementComplexEulerProduct

/-! ### The complex displacement surface -/

/-- The complex displacement term with the zero index removed explicitly. -/
noncomputable def dTermC (s w : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (nS n : ℂ) ^ (-s) * (n : ℂ) ^ (-w)

@[simp]
theorem dterm_c_zero (s w : ℂ) : dTermC s w 0 = 0 := if_pos rfl

@[simp]
theorem dterm_c_one (s w : ℂ) : dTermC s w 1 = 1 := by
  simp [dTermC, nS_one]

/-- On positive natural bases the complex norm remembers only the real parts of
the two exponents, recovering the frozen real displacement term exactly. -/
theorem dterm_c_norm (s w : ℂ) (n : ℕ) :
    ‖dTermC s w n‖ = dTerm s.re w.re n := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [dterm_c_zero, dTerm_zero]
    simp
  have hnSpos : 0 < nS n := Nat.pos_of_ne_zero (nS_ne_zero n)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  rw [dTermC, dTerm, if_neg hn, if_neg hn, norm_mul,
    Complex.norm_natCast_cpow_of_pos hnSpos,
    Complex.norm_natCast_cpow_of_pos hnpos]
  simp

/-- The complex displacement term inherits coprime multiplicativity from the
hidden product and the positive-natural-base cpow multiplication law. -/
theorem dterm_c_mul_of_coprime {s w : ℂ} {m n : ℕ} (h : Nat.Coprime m n) :
    dTermC s w (m * n) = dTermC s w m * dTermC s w n := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hn : n = 1 := Nat.coprime_zero_left n |>.mp h
    subst hn
    simp
  rcases eq_or_ne n 0 with rfl | hn
  · have hm' : m = 1 := Nat.coprime_zero_right m |>.mp h
    subst hm'
    simp
  have hmn : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  unfold dTermC
  rw [if_neg hmn, if_neg hm, if_neg hn, nS_mul_of_coprime h]
  push_cast
  rw [
    Complex.natCast_mul_natCast_cpow, Complex.natCast_mul_natCast_cpow]
  ring

/-- Absolute convergence follows without new estimates from the frozen real
summability theorem and the exact norm identity. -/
theorem dterm_c_summable {s w : ℂ} (hs : 0 ≤ s.re) (hsw : 1 < (s + w).re) :
    Summable (fun n : ℕ => ‖dTermC s w n‖) := by
  have hreal : Summable (fun n : ℕ => ‖dTerm s.re w.re n‖) :=
    dTerm_summable hs (by simpa using hsw)
  simpa only [dterm_c_norm, Real.norm_of_nonneg (dTerm_nonneg _ _ _)] using hreal

/-- On a prime power the complex displacement term is the complex
Hecke-Mahler monomial. -/
theorem dterm_c_prime_pow {s w : ℂ} {p : ℕ} (hp : p.Prime) (e : ℕ) :
    dTermC s w (p ^ e) =
      ((p : ℂ) ^ (-s)) ^ goldenSubstStart e * ((p : ℂ) ^ (-w)) ^ e := by
  have hne : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  unfold dTermC
  rw [if_neg hne, nS_prime_pow hp]
  push_cast
  rw [← Complex.natCast_cpow_natCast_mul p (goldenSubstStart e) (-s),
    ← Complex.natCast_cpow_natCast_mul p e (-w),
    Complex.cpow_nat_mul, Complex.cpow_nat_mul]

/-- **Complex Euler product of the displacement surface.** This is only an
identity on the half-plane where the defining Dirichlet series converges
absolutely. -/
theorem complex_displacement_euler_product {s w : ℂ}
    (hs : 0 ≤ s.re) (hsw : 1 < (s + w).re) :
    ∏' p : Nat.Primes,
        (∑' e : ℕ,
          ((p : ℂ) ^ (-s)) ^ goldenSubstStart e * ((p : ℂ) ^ (-w)) ^ e)
      = ∑' n : ℕ, dTermC s w n := by
  have hEuler := EulerProduct.eulerProduct_tprod (f := dTermC s w) (dterm_c_one s w)
    (fun {m n} h => dterm_c_mul_of_coprime h) (dterm_c_summable hs hsw)
    (dterm_c_zero s w)
  rw [← hEuler]
  exact tprod_congr fun p => tsum_congr fun e => (dterm_c_prime_pow p.prop e).symm

/-! ### The convergent golden germ section -/

/-- The analytic exponent account is exactly the substitution start minus its
golden-conjugate linear component. -/
theorem o5_beta_eq_substitution_start_sub_conjugate (e : ℕ) :
    o5Beta e = (goldenSubstStart e : ℝ) - (e : ℝ) * Real.goldenConj := by
  have hbeattyInt : (goldenSubstStart e : ℤ) =
      ⌊((e : ℝ) + 1) * Real.goldenRatio⌋ - 1 := by
    rw [golden_subst_start_eq_displacement_decode]
    exact displacement_decode_eq_beatty_floor e
  have hbeattyReal := congrArg (fun z : ℤ => (z : ℝ)) hbeattyInt
  push_cast at hbeattyReal
  rw [o5Beta, Real.one_sub_goldenConj]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← hbeattyReal]

/-- At `w = -goldenConj * s`, every prime-power displacement term is the
golden Euler germ monomial with exponent `o5Beta`. -/
theorem dterm_c_prime_pow_germ_section {s : ℂ} {p : ℕ} (hp : p.Prime) (e : ℕ) :
    dTermC s (-((Real.goldenConj : ℂ)) * s) (p ^ e) =
      (p : ℂ) ^ (-s * (o5Beta e : ℂ)) := by
  rw [dterm_c_prime_pow hp e, ← Complex.cpow_nat_mul, ← Complex.cpow_nat_mul,
    ← Complex.cpow_add _ _ (by exact_mod_cast hp.ne_zero)]
  rw [o5_beta_eq_substitution_start_sub_conjugate]
  push_cast
  congr 1
  ring

/-- The convergent golden germ is the golden-conjugate section of the complex
displacement Euler product. No continuation beyond this half-plane is asserted. -/
theorem complex_displacement_germ_section {s : ℂ}
    (hs : 1 < Real.goldenRatio * s.re) :
    ∏' p : Nat.Primes, (∑' e : ℕ, (p : ℂ) ^ (-s * (o5Beta e : ℂ))) =
      ∑' n : ℕ, dTermC s (-((Real.goldenConj : ℂ)) * s) n := by
  have hsnonneg : 0 ≤ s.re := by
    nlinarith [Real.goldenRatio_pos]
  have hsection :
      (s + (-((Real.goldenConj : ℂ)) * s)).re = Real.goldenRatio * s.re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    rw [← Real.one_sub_goldenRatio]
    ring
  have hconv : 1 < (s + (-((Real.goldenConj : ℂ)) * s)).re := by
    rwa [hsection]
  rw [← complex_displacement_euler_product hsnonneg hconv]
  exact tprod_congr fun p => tsum_congr fun e =>
    (dterm_c_prime_pow_germ_section p.prop e).symm.trans (dterm_c_prime_pow p.prop e)

example : dTermC 1 1 1 = 1 := by simp

end GoldenDisplacementComplexEulerProduct

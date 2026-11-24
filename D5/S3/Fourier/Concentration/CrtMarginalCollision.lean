/- GID: D5/S3/Fourier/Concentration/CrtMarginalCollision
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/CrtMarginalCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equal marginal collision profiles can give opposite errors under multiplication. -/

import D5.S3.Fourier.Concentration.CyclicCollisionCertificate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Finset
open D5.S3.Fourier.FinitePoisson (character character_apply)
open D5.S3.Fourier.Concentration.CyclicCollisionCertificate

namespace D5.S3.Fourier.Concentration.CrtMarginalCollision

noncomputable section

private theorem norm_affine_real (a b : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(a : ℂ) + (b : ℂ) * z‖ ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b * z.re := by
  have hs : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz, one_pow, Complex.normSq_apply] at h
    nlinarith only [h]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
  linear_combination b ^ 2 * hs

private theorem norm_six_char_affine (a b : ℝ) (n : ℤ) :
    ‖(a : ℂ) + (b : ℂ) * ZMod.stdAddChar (N := 6) (n : ZMod 6)‖ ^ 2 =
      a ^ 2 + b ^ 2 + 2 * a * b * Real.cos ((n : ℝ) * Real.pi / 3) := by
  let χ := ZMod.stdAddChar (N := 6)
  rw [norm_affine_real _ _ _ (χ.norm_apply _), ZMod.stdAddChar_coe, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

private theorem mixed_residues_gap (p : ℕ) (hp : 0 < p) :
    let A := (1 + (1 / 4 : ℝ) ^ p) / 2 * ((1 + 2 * (7 / 16 : ℝ) ^ p) / 3)
    let F (r : ℝ) := (1 + (1 / 4 : ℝ) ^ p + 2 * (7 / 16 : ℝ) ^ p + 2 * r ^ p) / 6
    F (1 / 16) < A ∧ A < F (13 / 16) ∧
      F (1 / 16) - A = ((1 / 16 : ℝ) ^ p - (7 / 64 : ℝ) ^ p) / 3 ∧
      F (13 / 16) - A = ((13 / 16 : ℝ) ^ p - (7 / 64 : ℝ) ^ p) / 3 := by
  dsimp only
  have hmul : (7 / 64 : ℝ) ^ p = (1 / 4 : ℝ) ^ p * (7 / 16 : ℝ) ^ p := by
    rw [show (7 / 64 : ℝ) = (1 / 4) * (7 / 16) by norm_num, mul_pow]
  have hleft : (1 / 16 : ℝ) ^ p < (7 / 64 : ℝ) ^ p :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) hp.ne'
  have hright : (7 / 64 : ℝ) ^ p < (13 / 16 : ℝ) ^ p :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) hp.ne'
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [hmul] at * <;> ring_nf at * <;> linarith


private def coordinatesP (j : Fin 3) : ℤ := ![0, 3, 4] j
private def coordinatesQ (j : Fin 3) : ℤ := ![0, 1, 0] j
private def weightsP (j : Fin 3) : ℝ := ![1 / 2, 1 / 4, 1 / 4] j
private def weightsQ (j : Fin 3) : ℝ := ![3 / 4, 1 / 4, 0] j

private def amplitude {q : ℕ} [NeZero q] (a : Fin 3 → ℤ) (w : Fin 3 → ℝ)
    (k : ZMod q) : ℂ := ∑ j, (w j : ℂ) * character k (a j : ZMod q)

private theorem collision_zero_from_power {q : ℕ} [NeZero q]
    (a : Fin 3 → ℤ) (w : Fin 3 → ℝ) (p : ℕ) :
    (q : ℝ) * cyclicCollisionMass q a w p {0} =
      ∑ k : ZMod q, (‖amplitude a w k‖ ^ 2) ^ p := by
  have h := congrArg Complex.re (cyclicCollisionMass_fourier q a w p {0})
  simpa [amplitude, character_apply, pow_mul, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.re_sum] using h

private theorem P_six_amplitude (k : ZMod 6) :
    amplitude coordinatesP weightsP k =
      (1 / 2 : ℂ) + (1 / 4 : ℂ) * ZMod.stdAddChar (k * 3) +
        (1 / 4 : ℂ) * ZMod.stdAddChar (k * 4) := by
  simp [amplitude, coordinatesP, weightsP, character_apply, Fin.sum_univ_three]

private theorem Q_amplitude {q : ℕ} [NeZero q] (k : ZMod q) :
    amplitude coordinatesQ weightsQ k = (3 / 4 : ℂ) + (1 / 4 : ℂ) * ZMod.stdAddChar k := by
  simp [amplitude, coordinatesQ, weightsQ, character_apply, Fin.sum_univ_three]

private theorem chi_six_three : ZMod.stdAddChar (3 : ZMod 6) = (-1 : ℂ) := by
  rw [show (3 : ZMod 6) = ((3 : ℤ) : ZMod 6) by norm_num, ZMod.stdAddChar_coe]
  norm_num
  rw [show (2 : ℂ) * Real.pi * Complex.I * 3 / 6 = Real.pi * Complex.I by ring,
    Complex.exp_pi_mul_I]

private theorem chi_six_three_mul (k : ℕ) :
    ZMod.stdAddChar ((k : ZMod 6) * 3) = (-1 : ℂ) ^ k := by
  rw [show (k : ZMod 6) * 3 = k • (3 : ZMod 6) by rw [nsmul_eq_mul]]
  rw [AddChar.map_nsmul_eq_pow, chi_six_three]

private theorem sum_zmod_fin {q : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    ∑ k, f k = ∑ k : Fin q, f (ZMod.finEquiv q k) :=
  ((ZMod.finEquiv q).toEquiv.sum_comp f).symm

private theorem cos_integer_one_third (n : ℤ) :
    Real.cos ((n : ℝ) * Real.pi / 3) =
      if n % 6 = 0 then 1 else if n % 6 = 1 ∨ n % 6 = 5 then 1 / 2
      else if n % 6 = 2 ∨ n % 6 = 4 then -1 / 2 else -1 := by
  have hreduce : Real.cos ((n : ℝ) * Real.pi / 3) =
      Real.cos (((n % 6 : ℤ) : ℝ) * Real.pi / 3) := by
    have hexp : (n : ℝ) * Real.pi / 3 =
        ((n % 6 : ℤ) : ℝ) * Real.pi / 3 + (n / 6 : ℤ) * (2 * Real.pi) := by
      have h : (n : ℝ) = ((n % 6 : ℤ) : ℝ) + 6 * ((n / 6 : ℤ) : ℝ) := by
        exact_mod_cast (Int.emod_add_mul_ediv n 6).symm
      linear_combination Real.pi / 3 * h
    rw [hexp, Real.cos_add_int_mul_two_pi]
  rw [hreduce]
  have hh := Int.emod_nonneg n (by decide : (6 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos n (by decide : 0 < (6 : ℤ))
  interval_cases h : n % 6 <;> norm_num
  · rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  · rw [show 4 * Real.pi / 3 = Real.pi / 3 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_three]
  · rw [show 5 * Real.pi / 3 = -(Real.pi / 3) + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.cos_neg, Real.cos_pi_div_three]

private theorem P_six_norm (n : ℕ) :
    ‖amplitude coordinatesP weightsP (n : ZMod 6)‖ ^ 2 =
      let a := 1 / 2 + (1 / 4 : ℝ) * (-1 : ℝ) ^ n
      a ^ 2 + (1 / 4 : ℝ) ^ 2 + 2 * a * (1 / 4) *
        Real.cos (((4 * (n : ℤ) : ℤ) : ℝ) * Real.pi / 3) := by
  rw [P_six_amplitude, chi_six_three_mul]
  have harg : (n : ZMod 6) * 4 = ((4 * (n : ℤ) : ℤ) : ZMod 6) := by
    push_cast
    ring
  rw [harg]
  let a := 1 / 2 + (1 / 4 : ℝ) * (-1 : ℝ) ^ n
  have ha : (a : ℂ) = (1 / 2 : ℂ) + (1 / 4) * (-1) ^ n := by
    push_cast [a]
    rfl
  have h := norm_six_char_affine a (1 / 4) (4 * (n : ℤ))
  push_cast only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  rwa [ha] at h

private theorem Q_six_norm (n : ℕ) :
    ‖amplitude coordinatesQ weightsQ (n : ZMod 6)‖ ^ 2 =
      (3 / 4 : ℝ) ^ 2 + (1 / 4 : ℝ) ^ 2 + 2 * (3 / 4) * (1 / 4) *
        Real.cos (((n : ℤ) : ℝ) * Real.pi / 3) := by
  simpa [Q_amplitude] using norm_six_char_affine (3 / 4) (1 / 4) (n : ℤ)

private theorem finEquiv_six_eq (j : Fin 6) : ZMod.finEquiv 6 j = (j.val : ZMod 6) := by
  fin_cases j <;> rfl

private theorem P_six_mass (p : ℕ) :
    cyclicCollisionMass 6 coordinatesP weightsP p {0} =
      (1 + (1 / 4 : ℝ) ^ p + 2 * (7 / 16 : ℝ) ^ p + 2 * (1 / 16 : ℝ) ^ p) / 6 := by
  have h := collision_zero_from_power (q := 6) coordinatesP weightsP p
  rw [sum_zmod_fin] at h
  simp only [finEquiv_six_eq, P_six_norm, cos_integer_one_third] at h
  simp_rw [Fin.sum_univ_succ] at h
  norm_num at h
  linarith

private theorem Q_six_mass (p : ℕ) :
    cyclicCollisionMass 6 coordinatesQ weightsQ p {0} =
      (1 + (1 / 4 : ℝ) ^ p + 2 * (7 / 16 : ℝ) ^ p + 2 * (13 / 16 : ℝ) ^ p) / 6 := by
  have h := collision_zero_from_power (q := 6) coordinatesQ weightsQ p
  rw [sum_zmod_fin] at h
  simp only [finEquiv_six_eq, Q_six_norm, cos_integer_one_third] at h
  simp_rw [Fin.sum_univ_succ] at h
  norm_num at h
  linarith

private theorem P_two_amplitude (k : ZMod 2) :
    amplitude coordinatesP weightsP k =
      (3 / 4 : ℂ) + (1 / 4 : ℂ) * ZMod.stdAddChar k := by
  simp [amplitude, coordinatesP, weightsP, character_apply, Fin.sum_univ_three,
    show (3 : ZMod 2) = 1 by decide, show (4 : ZMod 2) = 0 by decide]
  ring

private theorem P_three_amplitude (k : ZMod 3) :
    amplitude coordinatesP weightsP k =
      (3 / 4 : ℂ) + (1 / 4 : ℂ) * ZMod.stdAddChar k := by
  simp [amplitude, coordinatesP, weightsP, character_apply, Fin.sum_univ_three,
    show (3 : ZMod 3) = 0 by decide, show (4 : ZMod 3) = 1 by decide]
  ring

private theorem chi_restrict_two (n : ℕ) :
    ZMod.stdAddChar (n : ZMod 2) = ZMod.stdAddChar ((3 * (n : ℤ) : ℤ) : ZMod 6) := by
  rw [← Int.cast_natCast, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private theorem chi_restrict_three (n : ℕ) :
    ZMod.stdAddChar (n : ZMod 3) = ZMod.stdAddChar ((2 * (n : ℤ) : ℤ) : ZMod 6) := by
  rw [← Int.cast_natCast, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private theorem Q_two_norm (n : ℕ) :
    ‖amplitude coordinatesQ weightsQ (n : ZMod 2)‖ ^ 2 =
      (3 / 4 : ℝ) ^ 2 + (1 / 4 : ℝ) ^ 2 + 2 * (3 / 4) * (1 / 4) *
        Real.cos (((3 * (n : ℤ) : ℤ) : ℝ) * Real.pi / 3) := by
  rw [Q_amplitude, chi_restrict_two]
  simpa using norm_six_char_affine (3 / 4) (1 / 4) (3 * (n : ℤ))

private theorem Q_three_norm (n : ℕ) :
    ‖amplitude coordinatesQ weightsQ (n : ZMod 3)‖ ^ 2 =
      (3 / 4 : ℝ) ^ 2 + (1 / 4 : ℝ) ^ 2 + 2 * (3 / 4) * (1 / 4) *
        Real.cos (((2 * (n : ℤ) : ℤ) : ℝ) * Real.pi / 3) := by
  rw [Q_amplitude, chi_restrict_three]
  simpa using norm_six_char_affine (3 / 4) (1 / 4) (2 * (n : ℤ))

private theorem Q_two_mass (p : ℕ) :
    cyclicCollisionMass 2 coordinatesQ weightsQ p {0} = (1 + (1 / 4 : ℝ) ^ p) / 2 := by
  have h := collision_zero_from_power (q := 2) coordinatesQ weightsQ p
  rw [sum_zmod_fin] at h
  have hcast (k : Fin 2) : ZMod.finEquiv 2 k = (k.val : ZMod 2) := by fin_cases k <;> rfl
  simp only [hcast, Q_two_norm, cos_integer_one_third] at h
  simp_rw [Fin.sum_univ_succ] at h
  norm_num at h
  linarith

private theorem Q_three_mass (p : ℕ) :
    cyclicCollisionMass 3 coordinatesQ weightsQ p {0} = (1 + 2 * (7 / 16 : ℝ) ^ p) / 3 := by
  have h := collision_zero_from_power (q := 3) coordinatesQ weightsQ p
  rw [sum_zmod_fin] at h
  have hcast (k : Fin 3) : ZMod.finEquiv 3 k = (k.val : ZMod 3) := by fin_cases k <;> rfl
  simp only [hcast, Q_three_norm, cos_integer_one_third] at h
  simp_rw [Fin.sum_univ_succ] at h
  norm_num at h
  linarith

/-- Equal marginal collision profiles can give opposite errors under multiplication. -/
theorem crt_marginal_collision_gap (p : ℕ) (hp : 0 < p) :
    let coordinatesP : Fin 3 → ℤ := ![0, 3, 4]
    let weightsP : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]
    let coordinatesQ : Fin 3 → ℤ := ![0, 1, 0]
    let weightsQ : Fin 3 → ℝ := ![3 / 4, 1 / 4, 0]
    let mixedQ := (fun n : ℕ => (13 / 16 : ℝ) ^ n) p
    let A := cyclicCollisionMass 2 coordinatesP weightsP p {0}
    let B := cyclicCollisionMass 3 coordinatesP weightsP p {0}
    A = cyclicCollisionMass 2 coordinatesQ weightsQ p {0} ∧
    B = cyclicCollisionMass 3 coordinatesQ weightsQ p {0} ∧
    cyclicCollisionMass 6 coordinatesP weightsP p {0} < A * B ∧
    A * B < cyclicCollisionMass 6 coordinatesQ weightsQ p {0} ∧
    cyclicCollisionMass 6 coordinatesP weightsP p {0} - A * B =
      ((1 / 16 : ℝ) ^ p - (7 / 64 : ℝ) ^ p) / 3 ∧
    cyclicCollisionMass 6 coordinatesQ weightsQ p {0} - A * B =
      (mixedQ - (7 / 64 : ℝ) ^ p) / 3 := by
  change
      let A := cyclicCollisionMass 2 coordinatesP weightsP p {0}
      let B := cyclicCollisionMass 3 coordinatesP weightsP p {0}
      A = cyclicCollisionMass 2 coordinatesQ weightsQ p {0} ∧
      B = cyclicCollisionMass 3 coordinatesQ weightsQ p {0} ∧
      cyclicCollisionMass 6 coordinatesP weightsP p {0} < A * B ∧
      A * B < cyclicCollisionMass 6 coordinatesQ weightsQ p {0} ∧
      cyclicCollisionMass 6 coordinatesP weightsP p {0} - A * B =
        ((1 / 16 : ℝ) ^ p - (7 / 64 : ℝ) ^ p) / 3 ∧
      cyclicCollisionMass 6 coordinatesQ weightsQ p {0} - A * B =
        ((13 / 16 : ℝ) ^ p - (7 / 64 : ℝ) ^ p) / 3
  dsimp only
  have htwo : cyclicCollisionMass 2 coordinatesP weightsP p {0} =
      cyclicCollisionMass 2 coordinatesQ weightsQ p {0} := by
    have a := collision_zero_from_power (q := 2) coordinatesP weightsP p
    have b := collision_zero_from_power (q := 2) coordinatesQ weightsQ p
    simp only [P_two_amplitude] at a
    simp only [Q_amplitude] at b
    norm_num at a b
    linarith
  have hthree : cyclicCollisionMass 3 coordinatesP weightsP p {0} =
      cyclicCollisionMass 3 coordinatesQ weightsQ p {0} := by
    have a := collision_zero_from_power (q := 3) coordinatesP weightsP p
    have b := collision_zero_from_power (q := 3) coordinatesQ weightsQ p
    simp only [P_three_amplitude] at a
    simp only [Q_amplitude] at b
    norm_num at a b
    linarith
  refine ⟨htwo, hthree, ?_⟩
  rw [htwo, hthree, P_six_mass, Q_six_mass, Q_two_mass, Q_three_mass]
  exact mixed_residues_gap p hp

end

end D5.S3.Fourier.Concentration.CrtMarginalCollision

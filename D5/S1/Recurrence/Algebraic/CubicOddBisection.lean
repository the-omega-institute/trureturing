/- GID: D5/S1/Recurrence/Algebraic/CubicOddBisection
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/CubicOddBisection
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Polynomial elimination identifies the odd coefficients of two algebraic series. -/

import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

open PowerSeries
namespace D5.S1.Recurrence.Algebraic.CubicOddBisection
private abbrev PS := PowerSeries ℚ
private def Agree (d : ℕ) (f g : PS) : Prop := ∀ n < d, coeff n f = coeff n g
private theorem agree_iff (d : ℕ) (f g : PS) :
    Agree d f g ↔ (X : PS) ^ d ∣ f - g := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]
private noncomputable def step (c : PS) (p : Polynomial PS) (f : PS) : PS :=
  c + X * p.eval f
private theorem step_agree (c : PS) (p : Polynomial PS) {d : ℕ} {f g : PS}
    (h : Agree d f g) : Agree (d + 1) (step c p f) (step c p g) := by
  apply (agree_iff _ _ _).mpr
  have hp := ((agree_iff _ _ _).mp h).trans (Polynomial.sub_dvd_eval_sub f g p)
  have hx := mul_dvd_mul_left (X : PS) hp
  simpa only [step, pow_succ', mul_sub, add_sub_add_left_eq_sub] using hx
private noncomputable def approximation (c : PS) (p : Polynomial PS) : ℕ → PS
  | 0 => c
  | k + 1 => step c p (approximation c p k)
private theorem approximation_stable (c : PS) (p : Polynomial PS) {d k : ℕ}
    (h : d ≤ k) : Agree d (approximation c p d) (approximation c p k) := by
  induction d generalizing k with
  | zero => intro n hn; omega
  | succ d ih =>
    cases k with
    | zero => omega
    | succ k => exact step_agree c p (ih (by omega))
private noncomputable def fixedSeries (c : PS) (p : Polynomial PS) : PS :=
  mk (fun n => coeff n (approximation c p (n + 1)))
private theorem fixed_agree (c : PS) (p : Polynomial PS) (d : ℕ) :
    Agree d (fixedSeries c p) (approximation c p d) := by
  intro n hn
  simpa only [fixedSeries, coeff_mk] using
    approximation_stable c p (by omega : n + 1 ≤ d) n (by omega)
private theorem fixed_equation (c : PS) (p : Polynomial PS) :
    fixedSeries c p = c + X * p.eval (fixedSeries c p) := by
  ext n
  exact (fixed_agree c p (n + 2) n (by omega)).trans
    (step_agree c p (fixed_agree c p (n + 1)) n (by omega)).symm

private noncomputable def pA : Polynomial PS :=
  3 * Polynomial.X - Polynomial.X ^ 2 +
    Polynomial.C (3 * X) * Polynomial.X ^ 2 +
    Polynomial.C (2 * X ^ 2) * Polynomial.X ^ 3
private noncomputable def pB : Polynomial PS :=
  8 * Polynomial.X ^ 2 - 3 * Polynomial.X - Polynomial.C (16 * X) * Polynomial.X ^ 3

private theorem pA_eval (f : PS) :
    pA.eval f = 3 * f - f ^ 2 + 3 * X * f ^ 2 + 2 * X ^ 2 * f ^ 3 := by
  simp [pA]
private theorem pB_eval (f : PS) :
    pB.eval f = 8 * f ^ 2 - 3 * f - 16 * X * f ^ 3 := by
  simp [pB]

/-- The branch at 1 of xA³-A²+3xA+1=0, constructed by coefficient iteration. -/
noncomputable def A : PowerSeries ℚ := 1 + 2 * X * fixedSeries 1 pA
/-- The normalized inverse series, constructed independently by its own equation. -/
noncomputable def B : PowerSeries ℚ := fixedSeries 1 pB

theorem A_equation : constantCoeff A = 1 ∧ X * A ^ 3 - A ^ 2 + 3 * X * A + 1 = 0 := by
  refine ⟨by simp [A], ?_⟩
  have h := fixed_equation 1 pA
  rw [pA_eval] at h
  dsimp only [A]
  linear_combination -4 * X * h

theorem B_equation : constantCoeff B = 1 ∧ B * (1 - 4 * X * B) ^ 2 = 1 - 3 * X * B := by
  have h := fixed_equation 1 pB
  rw [pB_eval] at h
  change B = 1 + X * (8 * B ^ 2 - 3 * B - 16 * X * B ^ 3) at h
  refine ⟨?_, ?_⟩
  · have hc := congrArg constantCoeff h
    simpa using hc
  · linear_combination h

theorem A_unique (f : PowerSeries ℚ) (h0 : constantCoeff f = 1)
    (hf : X * f ^ 3 - f ^ 2 + 3 * X * f + 1 = 0) : f = A := by
  let q := X * (f ^ 2 + f * A + A ^ 2) - (f + A) + 3 * X
  have hq : q ≠ 0 := by
    intro hz
    have hc := congrArg constantCoeff hz
    norm_num [q, h0, A_equation.1] at hc
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show (f - A) * q = 0 by
    dsimp [q]
    linear_combination hf - A_equation.2)).resolve_right hq

theorem B_unique (f : PowerSeries ℚ)
    (hf : f * (1 - 4 * X * f) ^ 2 = 1 - 3 * X * f) : f = B := by
  let q := 1 + 3 * X - 8 * X * (f + B) + 16 * X ^ 2 * (f ^ 2 + f * B + B ^ 2)
  have hq : q ≠ 0 := by
    intro hz
    have hc := congrArg constantCoeff hz
    norm_num [q] at hc
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show (f - B) * q = 0 by
    dsimp [q]
    linear_combination hf - B_equation.2)).resolve_right hq

private theorem cubic_pair_sum (u v : PS) (h0 : constantCoeff (u - v) ≠ 0)
    (hu : X * u ^ 3 - u ^ 2 + 3 * X * u + 1 = 0)
    (hv : X * v ^ 3 - v ^ 2 + 3 * X * v + 1 = 0) :
    (u + v) * (1 - X * (u + v)) ^ 2 = 4 * X - 3 * X ^ 2 * (u + v) := by
  have hne : u - v ≠ 0 := by
    intro hz
    exact h0 (by rw [hz, map_zero])
  have hq : X * (u ^ 2 + u * v + v ^ 2) - (u + v) + 3 * X = 0 := by
    apply (mul_eq_zero.mp (show (u - v) *
      (X * (u ^ 2 + u * v + v ^ 2) - (u + v) + 3 * X) = 0 by
        linear_combination hu - hv)).resolve_left hne
  have hp : u * v * (1 - X * (u + v)) + 1 = 0 := by
    linear_combination hu - u * hq
  linear_combination -(1 - X * (u + v)) * hq - X * hp

private theorem sum_equation_unique (s z : PS)
    (hs : s * (1 - X * s) ^ 2 = 4 * X - 3 * X ^ 2 * s)
    (hz : z * (1 - X * z) ^ 2 = 4 * X - 3 * X ^ 2 * z) : s = z := by
  let q := 1 - 2 * X * (s + z) + X ^ 2 * (s ^ 2 + s * z + z ^ 2) + 3 * X ^ 2
  have hq : q ≠ 0 := by
    intro he
    have hc := congrArg constantCoeff he
    norm_num [q] at hc
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show (s - z) * q = 0 by
    dsimp [q]
    linear_combination hs - hz)).resolve_right hq

private theorem odd_series_identity : A - rescale (-1) A = 4 * X * expand 2 (by decide) B := by
  have hconstant : constantCoeff (rescale (-1 : ℚ) A) = 1 := by
    simpa only [coeff_zero_eq_constantCoeff, pow_zero, one_mul] using
      (coeff_rescale A (-1) 0).trans (by simp [A_equation.1])
  have hv : X * (-rescale (-1 : ℚ) A) ^ 3 - (-rescale (-1 : ℚ) A) ^ 2 +
      3 * X * (-rescale (-1 : ℚ) A) + 1 = 0 := by
    have he := congrArg (rescale (-1 : ℚ)) A_equation.2
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_zero,
      rescale_neg_one_X] at he
    linear_combination he
  have hs := cubic_pair_sum A (-rescale (-1 : ℚ) A) (by
    simp only [map_sub, map_neg, A_equation.1, hconstant]
    norm_num) A_equation.2 hv
  apply sum_equation_unique
  · simpa only [sub_eq_add_neg] using hs
  · have hb := congrArg (expand 2 (by decide : 2 ≠ 0) (R := ℚ)) B_equation.2
    simp only [map_mul, map_sub, map_one, map_ofNat, map_pow, expand_X] at hb
    linear_combination 4 * X * hb

/-- The odd-index coefficients of A372018 are twice the coefficients of A371364. -/
theorem odd_coeff_identity (n : ℕ) : coeff (2 * n + 1) A = 2 * coeff n B := by
  have h := congrArg (coeff (2 * n + 1)) odd_series_identity
  rw [show 4 * X * expand 2 (by decide) B = X * (C 4 * expand 2 (by decide) B) by
    simp only [map_ofNat]; ring] at h
  simp only [map_sub, coeff_rescale, coeff_succ_X_mul, coeff_C_mul, coeff_expand_mul] at h
  have hn : (-1 : ℚ) ^ (2 * n + 1) = -1 := by simp [pow_add, pow_mul]
  rw [hn] at h
  linear_combination h / 2

/-- The identity also holds for any witnesses of the two original equations. -/
theorem odd_coeff_identity_of_equations (f g : PowerSeries ℚ)
    (hf0 : constantCoeff f = 1)
    (hf : X * f ^ 3 - f ^ 2 + 3 * X * f + 1 = 0)
    (hg : g * (1 - 4 * X * g) ^ 2 = 1 - 3 * X * g) (n : ℕ) :
    coeff (2 * n + 1) f = 2 * coeff n g := by
  rw [A_unique f hf0 hf, B_unique g hg]
  exact odd_coeff_identity n

#print axioms odd_coeff_identity_of_equations

#print axioms A_equation
#print axioms B_equation
#print axioms A_unique
#print axioms B_unique
#print axioms odd_coeff_identity

end D5.S1.Recurrence.Algebraic.CubicOddBisection

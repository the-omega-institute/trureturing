/- GID: D5/S1/Recurrence/Periodic/EulerSignedFrequency
   generality: G
   mirror-B: D5/B/S1/Recurrence/Periodic/EulerSignedFrequency
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral signed Euler coefficients and finite odd-length frequency identities. -/

import D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Totient

/-! Integral coefficients of two signed Euler branches and their finite frequency sums. -/

set_option maxRecDepth 2048

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode eCoeff_encode eCoeff_ext)

namespace D5.S1.Recurrence.Periodic.EulerSignedFrequency

/-- Integer derivatives of `2 exp(b t)/(1 + exp(2 t))` at zero. -/
def A (b : ℕ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => (b : ℤ) ^ (n + 1) -
      ∑ i : Fin (n + 1), ((n + 1).choose i : ℤ) * 2 ^ (n - i.val) * A b i
termination_by n => n

/-- The exponential series of the integral signed coefficients. -/
noncomputable def F (b : ℕ) : PowerSeries ℚ := encode (fun n => (A b n : ℚ))

private theorem eCoeff_F (b n : ℕ) : eCoeff (F b) n = (A b n : ℚ) :=
  eCoeff_encode _ _

private theorem eCoeff_add (f g : PowerSeries ℚ) (n : ℕ) :
    eCoeff (f + g) n = eCoeff f n + eCoeff g n := by
  simp [eCoeff, mul_add]

private theorem eCoeff_C_mul (c : ℚ) (f : PowerSeries ℚ) (n : ℕ) :
    eCoeff (C c * f) n = c * eCoeff f n := by
  simp [eCoeff, mul_left_comm]

private theorem eCoeff_exp_pow (u n : ℕ) :
    eCoeff ((exp ℚ) ^ u) n = (u : ℚ) ^ n := by
  rw [exp_pow_eq_rescale_exp]
  simp only [eCoeff, coeff_rescale, coeff_exp]
  change (n.factorial : ℚ) * ((u : ℚ) ^ n * (1 / (n.factorial : ℚ))) = _
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- The defining exponential identity is proved from an integral recurrence. -/
theorem generating_identity (b : ℕ) :
    (1 + (exp ℚ) ^ 2) * F b = C 2 * (exp ℚ) ^ b := by
  apply eCoeff_ext
  intro n
  rw [eCoeff_C_mul, eCoeff_exp_pow, add_mul, one_mul, mul_comm ((exp ℚ) ^ 2),
    eCoeff_add, eCoeff_mul, eCoeff_F]
  cases n with
  | zero => norm_num [eCoeff_F, A]
  | succ n =>
    rw [sum_range_succ]
    simp only [Nat.choose_self, Nat.sub_self, Nat.cast_one, one_mul,
      eCoeff_F, eCoeff_exp_pow, pow_zero, mul_one]
    rw [A, Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    rw [Fin.sum_univ_eq_sum_range (fun i => ((n + 1).choose i : ℚ) *
      2 ^ (n - i) * (A b i : ℚ))]
    norm_num only [Nat.cast_ofNat]
    have hsum :
        (∑ i ∈ range (n + 1), ((n + 1).choose i : ℚ) * (A b i : ℚ) *
          (2 : ℚ) ^ (n + 1 - i)) =
        2 * ∑ i ∈ range (n + 1), ((n + 1).choose i : ℚ) *
          2 ^ (n - i) * (A b i : ℚ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [show n + 1 - i = (n - i) + 1 by have := mem_range.mp hi; omega,
        pow_succ]
      ring
    rw [hsum]
    ring

private theorem odd_geometric (x : PowerSeries ℚ) (L : ℕ) (hL : Odd L) :
    (1 + x) * (∑ h ∈ range L, (-1 : PowerSeries ℚ) ^ h * x ^ h) = 1 + x ^ L := by
  have h := mul_neg_geom_sum (-x) L
  have hs : (∑ h ∈ range L, (-x) ^ h) =
      ∑ h ∈ range L, (-1 : PowerSeries ℚ) ^ h * x ^ h := by
    apply sum_congr rfl
    intro h hh
    exact neg_pow x h
  rw [hs, hL.neg_pow, sub_neg_eq_add, sub_neg_eq_add] at h
  exact h

/-- Exact finite frequency formula, before modular reduction or division. -/
theorem finite_identity (b L : ℕ) (hL : Odd L) :
    (1 + (exp ℚ) ^ (2 * L)) * F b =
      C 2 * ∑ h ∈ range L, C ((-1 : ℚ) ^ h) * (exp ℚ) ^ (2 * h + b) := by
  have hg := odd_geometric ((exp ℚ) ^ 2) L hL
  have hz : 1 + (exp ℚ) ^ 2 ≠ 0 := by
    intro hz
    have := congrArg constantCoeff hz
    norm_num at this
  apply mul_left_cancel₀ hz
  calc
    (1 + (exp ℚ) ^ 2) * ((1 + (exp ℚ) ^ (2 * L)) * F b) =
        (1 + (exp ℚ) ^ (2 * L)) * (C 2 * (exp ℚ) ^ b) := by
      rw [← generating_identity b]
      ring
    _ = ((1 + (exp ℚ) ^ 2) *
        ∑ h ∈ range L, (-1 : PowerSeries ℚ) ^ h * ((exp ℚ) ^ 2) ^ h) *
          (C 2 * (exp ℚ) ^ b) := by rw [hg, ← pow_mul]
    _ = (1 + (exp ℚ) ^ 2) *
        (C 2 * ∑ h ∈ range L, C ((-1 : ℚ) ^ h) * (exp ℚ) ^ (2 * h + b)) := by
      rw [mul_assoc]
      congr 1
      simp only [sum_mul, mul_sum, map_pow, map_neg, map_one, pow_mul, pow_add]
      apply sum_congr rfl
      intro h hh
      ring

private theorem denominator_ne_zero : 1 + (exp ℚ) ^ 2 ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  norm_num at this

/-- Differential identities for the hyperbolic secant and tangent branches. -/
theorem branch_equations :
    PowerSeries.derivative (F 0) = F 0 * (F 0 - 2) ∧
    PowerSeries.derivative (F 1) = F 1 * (F 0 - 1) ∧
    (F 1) ^ 2 = F 0 * (2 - F 0) := by
  have h0 := generating_identity 0
  have h1 := generating_identity 1
  norm_num only [pow_zero, pow_one, mul_one, map_ofNat] at h0 h1
  have hdG : PowerSeries.derivative (1 + (exp ℚ) ^ 2) = 2 * (exp ℚ) ^ 2 := by
    simp only [map_add, derivative_one, derivative_pow, derivative_exp, smul_eq_mul]
    ring
  have hd0 := congrArg (PowerSeries.derivative (R := ℚ)) h0
  have hd1 := congrArg (PowerSeries.derivative (R := ℚ)) h1
  have hd2 : PowerSeries.derivative (2 : PowerSeries ℚ) = 0 := by
    change PowerSeries.derivative (C (2 : ℚ)) = 0
    exact derivative_C
  simp only [Derivation.leibniz, hdG, hd2, mul_zero, zero_add,
    derivative_exp, smul_eq_mul] at hd0 hd1
  refine ⟨?_, ?_, ?_⟩
  · apply mul_left_cancel₀ denominator_ne_zero
    linear_combination hd0 - F 0 * h0
  · apply mul_left_cancel₀ denominator_ne_zero
    linear_combination hd1 - F 1 * h0 - h1
  · apply mul_left_cancel₀ (pow_ne_zero 2 denominator_ne_zero)
    linear_combination ((1 + (exp ℚ) ^ 2) * F 1 + 2 * exp ℚ) * h1 -
      ((1 + (exp ℚ) ^ 2) * (2 - F 0) - 2) * h0

private theorem scaled_identity (b L u : ℕ) (hL : Odd L) :
    (1 + (exp ℚ) ^ (u * (2 * L))) * rescale (u : ℚ) (F b) =
      C 2 * ∑ h ∈ range L, C ((-1 : ℚ) ^ h) *
        (exp ℚ) ^ (u * (2 * h + b)) := by
  have h := congrArg (rescale (u : ℚ)) (finite_identity b L hL)
  have he : rescale (u : ℚ) (exp ℚ) = (exp ℚ) ^ u :=
    (exp_pow_eq_rescale_exp u).symm
  simpa only [map_mul, map_add, map_one, map_sum, map_pow, map_neg, map_ofNat,
    he, ← pow_mul] using h

private theorem eCoeff_scaled_F (b u j : ℕ) :
    eCoeff (rescale (u : ℚ) (F b)) j = (u : ℚ) ^ j * (A b j : ℚ) := by
  simp only [eCoeff, coeff_rescale]
  rw [mul_left_comm]
  exact congrArg ((u : ℚ) ^ j * ·) (eCoeff_F b j)

private theorem integer_moment (b L u j : ℕ) (hL : Odd L) :
    2 * ∑ h ∈ range L, (-1 : ℤ) ^ h * (u * (2 * h + b) : ℕ) ^ j =
      (u : ℤ) ^ j * A b j +
        ∑ i ∈ range (j + 1), (j.choose i : ℤ) *
          (u * (2 * L) : ℕ) ^ i * ((u : ℤ) ^ (j - i) * A b (j - i)) := by
  have h := congrArg (fun f => eCoeff f j) (scaled_identity b L u hL)
  rw [add_mul, one_mul, eCoeff_add, eCoeff_scaled_F, eCoeff_mul] at h
  simp only [eCoeff_exp_pow, eCoeff_scaled_F, eCoeff_C_mul] at h
  have hr : eCoeff (∑ h ∈ range L, C ((-1 : ℚ) ^ h) *
      (exp ℚ) ^ (u * (2 * h + b))) j =
      ∑ h ∈ range L, (-1 : ℚ) ^ h * (u * (2 * h + b) : ℕ) ^ j := by
    simp only [eCoeff, map_sum, mul_sum, coeff_C_mul]
    apply sum_congr rfl
    intro h hh
    rw [mul_left_comm]
    exact congrArg ((-1 : ℚ) ^ h * ·) (eCoeff_exp_pow _ _)
  rw [hr] at h
  exact_mod_cast h.symm

/-- Odd-length frequency sums can be reduced modulo every odd divisor of `u L`. -/
theorem scaled_moment (b L u q j : ℕ) (hL : Odd L) (hq : Odd q)
    (hdiv : q ∣ u * L) :
    (u : ZMod q) ^ j * (A b j : ZMod q) =
      ∑ h ∈ range L, (-1 : ZMod q) ^ h * (u * (2 * h + b) : ℕ) ^ j := by
  have h := congrArg (Int.castRingHom (ZMod q)) (integer_moment b L u j hL)
  simp only [map_add, map_mul, map_sum, map_pow, map_neg, map_one, map_ofNat,
    map_natCast, Int.coe_castRingHom] at h
  have hz : ((u * (2 * L) : ℕ) : ZMod q) = 0 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    exact hdiv.trans ⟨2, by ring⟩
  have hs : (∑ i ∈ range (j + 1), (j.choose i : ZMod q) *
      (u * (2 * L) : ℕ) ^ i * ((u : ZMod q) ^ (j - i) * (A b (j - i) : ZMod q))) =
        (u : ZMod q) ^ j * (A b j : ZMod q) := by
    rw [sum_eq_single 0]
    · simp
    · intro i hi hi0
      rw [hz, zero_pow hi0]
      ring
    · simp
  rw [hs] at h
  have htwo : IsUnit (2 : ZMod q) := by
    apply (ZMod.isUnit_iff_coprime 2 q).mpr
    exact hq.coprime_two_left
  apply htwo.mul_left_cancel
  linear_combination -h

end D5.S1.Recurrence.Periodic.EulerSignedFrequency

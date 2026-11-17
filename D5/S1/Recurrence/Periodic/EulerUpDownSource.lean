/- GID: D5/S1/Recurrence/Periodic/EulerUpDownSource
   generality: G
   mirror-B: D5/B/S1/Recurrence/Periodic/EulerUpDownSource
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The ordinary A000111 carrier with its exact source recurrence and differential equation. -/

import D5.S1.Recurrence.Periodic.EulerSignedFrequency
import D5.S1.Recurrence.Periodic.SecantNumberPurePeriodRefutation
import Mathlib.Basic.Complex.Basic

/-! Ordinary Euler up/down numbers use the positive recurrence in OEIS A000111. -/

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode eCoeff_encode eCoeff_ext)

namespace D5.S1.Recurrence.Periodic.EulerUpDownSource

/-- The offset-zero ordinary Euler up/down numbers, not the weighted Entringer diagonal. -/
def E : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => ∑ i : Fin (n + 1), (n.choose i) * E i * E (n + 1 - i.val)
termination_by n => n

private theorem E_step (n : ℕ) : E (n + 2) =
    ∑ i ∈ range (n + 1), n.choose i * E i * E (n + 1 - i) := by
  rw [E, Fin.sum_univ_eq_sum_range (fun i => n.choose i * E i * E (n + 1 - i))]

/-- The exponential generating series of the source-normalized natural carrier. -/
noncomputable def ordinarySeries : PowerSeries ℚ := encode (fun n => (E n : ℚ))

private theorem eCoeff_ordinary (n : ℕ) :
    eCoeff ordinarySeries n = (E n : ℚ) := eCoeff_encode _ _

/-- The source equation `A'' = A A'`, including its two initial conditions. -/
theorem source_equation : constantCoeff ordinarySeries = 1 ∧
    constantCoeff (PowerSeries.derivative ordinarySeries) = 1 ∧
    PowerSeries.derivative (PowerSeries.derivative ordinarySeries) =
      ordinarySeries * PowerSeries.derivative ordinarySeries := by
  refine ⟨by simp [ordinarySeries, E], ?_, ?_⟩
  · rw [← eCoeff_zero, eCoeff_derivative, eCoeff_ordinary]
    norm_num [E]
  · apply eCoeff_ext
    intro n
    rw [eCoeff_derivative, eCoeff_derivative, eCoeff_ordinary, eCoeff_mul,
      E_step, Nat.cast_sum]
    apply sum_congr rfl
    intro i hi
    rw [eCoeff_derivative, eCoeff_ordinary, eCoeff_ordinary]
    push_cast
    rw [show n + 1 - i = n - i + 1 by have := mem_range.mp hi; omega]

private theorem E_succ_le (n : ℕ) : E n ≤ E (n + 1) := by
  cases n with
  | zero => simp [E]
  | succ n =>
    rw [show n + 1 + 1 = n + 2 by omega, E_step]
    have h := single_le_sum (fun i (hi : i ∈ range (n + 1)) =>
      Nat.zero_le (n.choose i * E i * E (n + 1 - i)))
      (show 0 ∈ range (n + 1) by simp)
    simpa [E] using h

private theorem E_mono : Monotone E := monotone_nat_of_le_succ E_succ_le

private theorem E_four : E 4 = 5 := by
  norm_num [E, Fin.sum_univ_succ]

/-- The only values at most two occur among the first four indices. -/
theorem boundary_values : E 0 = 1 ∧ E 1 = 1 ∧ E 2 = 1 ∧ E 3 = 2 ∧
    ∀ k : ℕ, 4 ≤ k → 2 < E k := by
  refine ⟨by simp [E], by simp [E], ?_, ?_, ?_⟩
  · norm_num [E, Fin.sum_univ_succ]
  · norm_num [E, Fin.sum_univ_succ]
  · intro k hk
    have h := E_mono hk
    rw [E_four] at h
    omega

private theorem ordinary_riccati :
    2 * PowerSeries.derivative ordinarySeries = ordinarySeries ^ 2 + 1 := by
  have hd2 : PowerSeries.derivative (2 : PowerSeries ℚ) = 0 := by
    change PowerSeries.derivative (C (2 : ℚ)) = 0
    exact derivative_C
  have h : 2 * PowerSeries.derivative ordinarySeries - ordinarySeries ^ 2 = 1 := by
    apply PowerSeries.derivative.ext
    · simp only [map_sub, Derivation.leibniz, hd2, zero_mul, zero_add,
        derivative_pow, derivative_one, source_equation.2.2, smul_eq_mul]
      ring
    · norm_num [source_equation.1, source_equation.2.1,
        show constantCoeff (2 : PowerSeries ℚ) = 2 from map_ofNat constantCoeff 2]
  linear_combination h

private theorem derivative_map_complex (f : PowerSeries ℚ) :
    PowerSeries.derivative (map (algebraMap ℚ ℂ) f) =
      map (algebraMap ℚ ℂ) (PowerSeries.derivative f) := by
  ext n
  simp [coeff_derivative]

private theorem derivative_rescale_complex (c : ℂ) (f : PowerSeries ℂ) :
    PowerSeries.derivative (rescale c f) = C c * rescale c (PowerSeries.derivative f) := by
  ext n
  simp only [coeff_derivative, coeff_rescale, coeff_C_mul, pow_succ]
  ring

private theorem riccati_unique (f g : PowerSeries ℂ)
    (h0 : constantCoeff f = constantCoeff g)
    (hf : 2 * PowerSeries.derivative f = f ^ 2 + 1)
    (hg : 2 * PowerSeries.derivative g = g ^ 2 + 1) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff] using h0
    | succ n =>
      have hs : coeff n (f ^ 2 + 1) = coeff n (g ^ 2 + 1) := by
        simp only [pow_two, map_add, coeff_mul]
        congr 1
        apply sum_congr rfl
        intro ij hij
        have hij' := mem_antidiagonal.mp hij
        rw [ih ij.1 (by omega), ih ij.2 (by omega)]
      have h := (congrArg (coeff n) hf).trans (hs.trans (congrArg (coeff n) hg).symm)
      simp only [coeff_ofNat_mul, coeff_derivative] at h
      have hne : (2 : ℂ) * ((n : ℂ) + 1) ≠ 0 := by
        exact mul_ne_zero (by norm_num) (by exact_mod_cast Nat.succ_ne_zero n)
      apply mul_left_cancel₀ hne
      linear_combination h

private noncomputable def liftI (f : PowerSeries ℚ) : PowerSeries ℂ :=
  rescale Complex.I (map (algebraMap ℚ ℂ) f)

private theorem liftI_derivative (f : PowerSeries ℚ) :
    PowerSeries.derivative (liftI f) = C Complex.I * liftI (PowerSeries.derivative f) := by
  rw [liftI, derivative_rescale_complex, derivative_map_complex]
  rfl

private theorem complex_correspondence :
    map (algebraMap ℚ ℂ) ordinarySeries =
      liftI (EulerSignedFrequency.F 1) +
        C Complex.I * (liftI (EulerSignedFrequency.F 0) - 1) := by
  let c := liftI (EulerSignedFrequency.F 1)
  let v := liftI (EulerSignedFrequency.F 0) - 1
  have hc : PowerSeries.derivative c = C Complex.I * c * v := by
    dsimp [c, v]
    rw [liftI_derivative, EulerSignedFrequency.branch_equations.2.1]
    simp only [liftI, map_mul, map_sub, map_one]
    ring
  have hv : PowerSeries.derivative v = C Complex.I * (v ^ 2 - 1) := by
    dsimp [v]
    rw [map_sub, derivative_one, sub_zero, liftI_derivative,
      EulerSignedFrequency.branch_equations.1]
    simp only [liftI, map_mul, map_sub, map_ofNat]
    ring
  have hrel : c ^ 2 = 1 - v ^ 2 := by
    have h := congrArg liftI EulerSignedFrequency.branch_equations.2.2
    simp only [liftI, map_pow, map_mul, map_sub, map_ofNat] at h
    dsimp [c, v, liftI]
    linear_combination h
  apply riccati_unique
  · simp [ordinarySeries, liftI, EulerSignedFrequency.F, encode,
      EulerSignedFrequency.A, ← coeff_zero_eq_constantCoeff, coeff_map, E]
  · rw [derivative_map_complex]
    simpa only [map_mul, map_ofNat, map_add, map_pow, map_one] using
      congrArg (map (algebraMap ℚ ℂ)) ordinary_riccati
  · change 2 * PowerSeries.derivative (c + C Complex.I * v) =
      (c + C Complex.I * v) ^ 2 + 1
    have hI : (C Complex.I : PowerSeries ℂ) ^ 2 = -1 := by
      rw [← map_pow, Complex.I_sq, map_neg, map_one]
    simp only [map_add, Derivation.leibniz, derivative_C, zero_mul, add_zero, hc, hv]
    linear_combination -hrel + (v ^ 2 - 2) * hI

private theorem liftI_coefficient (b n : ℕ) :
    (n.factorial : ℂ) * coeff n (liftI (EulerSignedFrequency.F b)) =
      Complex.I ^ n * (EulerSignedFrequency.A b n : ℂ) := by
  have h := congrArg (algebraMap ℚ ℂ)
    (eCoeff_encode (fun j => (EulerSignedFrequency.A b j : ℚ)) n)
  simp only [map_mul, map_natCast, map_intCast] at h
  simp only [liftI, coeff_rescale, coeff_map, EulerSignedFrequency.F]
  rw [mul_left_comm]
  exact congrArg (Complex.I ^ n * ·) h

private theorem ordinary_coefficient_complex (n : ℕ) :
    (n.factorial : ℂ) * coeff n (map (algebraMap ℚ ℂ) ordinarySeries) = (E n : ℂ) := by
  have h := congrArg (algebraMap ℚ ℂ) (eCoeff_ordinary n)
  simpa only [eCoeff, map_mul, map_natCast, coeff_map] using h

private theorem complex_coefficient (n : ℕ) (hn : n ≠ 0) :
    (E n : ℂ) = Complex.I ^ n *
      ((EulerSignedFrequency.A 1 n : ℂ) + Complex.I * (EulerSignedFrequency.A 0 n : ℂ)) := by
  have h := congrArg (fun f => (n.factorial : ℂ) * coeff n f) complex_correspondence
  simp only [map_add, coeff_C_mul, map_sub, coeff_one, if_neg hn] at h
  have hc := liftI_coefficient 1 n
  have hv := liftI_coefficient 0 n
  rw [ordinary_coefficient_complex] at h
  linear_combination h + hc + Complex.I * hv

/-- The even signed branch is the ordinary secant coefficient with its exact sign. -/
theorem signed_even (s : ℕ) :
    (E (2 * s) : ℤ) = (-1 : ℤ) ^ s * EulerSignedFrequency.A 1 (2 * s) := by
  by_cases hs : s = 0
  · subst s
    simp [E, EulerSignedFrequency.A]
  · have h := complex_coefficient (2 * s) (by omega)
    rw [pow_mul, Complex.I_sq] at h
    have he : (-1 : ℂ) ^ s = (((-1 : ℤ) ^ s : ℤ) : ℂ) := by norm_cast
    rw [he] at h
    have hr := congrArg Complex.re h
    simp only [Complex.natCast_re, Complex.mul_re, Complex.add_re, Complex.intCast_re,
      Complex.intCast_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, mul_zero, sub_zero, zero_add, add_zero] at hr
    exact_mod_cast hr

/-- The odd signed branch retains the ordinary tangent coefficients. -/
theorem signed_odd (s : ℕ) :
    (E (2 * s + 1) : ℤ) = (-1 : ℤ) ^ (s + 1) *
      EulerSignedFrequency.A 0 (2 * s + 1) := by
  have h := complex_coefficient (2 * s + 1) (by omega)
  rw [pow_succ, pow_mul, Complex.I_sq] at h
  have he : (-1 : ℂ) ^ s = (((-1 : ℤ) ^ s : ℤ) : ℂ) := by norm_cast
  rw [he] at h
  have hr := congrArg Complex.re h
  simp only [Complex.natCast_re, Complex.mul_re, Complex.add_re, Complex.intCast_re,
    Complex.intCast_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, mul_zero, sub_zero, zero_add, add_zero, zero_sub] at hr
  rw [pow_succ]
  exact_mod_cast hr

end D5.S1.Recurrence.Periodic.EulerUpDownSource

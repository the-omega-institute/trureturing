/- GID: D5/S1/Recurrence/Periodic/EulerTwoPrimary
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/EulerTwoPrimary
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The ordinary Euler recurrence, signed and secant identifications, tangent valuation and secant parity. -/

/-
proof_shape: 9 definitions, 45 consumed bind-only theorems and 2 content theorems.
The content declarations are tangent_power and secant_odd. All other theorems are
bind-only after same-delivery inlining and reuse of the frozen contraction supplier.
escape_witness: tangent_power proves the uniform valuation induction using Lucas
binomial evenness; secant_odd proves the secant parity induction using tangent_power.
Both lie on the live path to EulerDivisorPropagation.two_primary.
admission_basis: escape-witness. The two final source assertions alone use the external
open-problem-resolution basis. Helper consumer arrows below run prerequisite -> consumer.
Direct frozen suppliers: QuarticEGFFixedPoint (encode, eCoeff_encode, eCoeff_ext),
PowerSeriesNormalizedContraction.exists_unique_fixed, UnitReversionSquareParity.agree_pow,
SecantNumberPurePeriodRefutation (a_unique, initial_values), and
ParametricExponentialSquareCongruence.linear_ode_unique. IntegralEGFComposition supplies
the coefficient interface through QuarticEGFFixedPoint. Other imports are pinned Mathlib.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/31291.
-/

import D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S1.Recurrence.Invariants.UnitReversionSquareParity
import D5.S1.Recurrence.Periodic.SecantNumberPurePeriodRefutation
import D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Lucas

open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
open D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction

/-! Ordinary Euler up/down numbers use the positive recurrence in OEIS A000111. -/

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode eCoeff_encode eCoeff_ext)

/-! Integral coefficients of two signed Euler branches and their finite frequency sums. -/

set_option maxRecDepth 2048

namespace D5.S1.Recurrence.Periodic.EulerSignedFrequency

/-- Integer derivatives of `2 exp(b t)/(1 + exp(2 t))` at zero. -/
/- proof_shape: definition; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.F. -/
def A (b : ℕ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => (b : ℤ) ^ (n + 1) -
      ∑ i : Fin (n + 1), ((n + 1).choose i : ℤ) * 2 ^ (n - i.val) * A b i
termination_by n => n

/-- The exponential series of the integral signed coefficients. -/
/- proof_shape: definition; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.generating_identity. -/
noncomputable def F (b : ℕ) : PowerSeries ℚ := encode (fun n => (A b n : ℚ))

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.generating_identity, D5.S1.Recurrence.Periodic.EulerSignedFrequency.eCoeff_scaled_F. -/
private theorem eCoeff_F (b n : ℕ) : eCoeff (F b) n = (A b n : ℚ) :=
  eCoeff_encode _ _

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.generating_identity, D5.S1.Recurrence.Periodic.EulerSignedFrequency.integer_moment. -/
private theorem eCoeff_add (f g : PowerSeries ℚ) (n : ℕ) :
    eCoeff (f + g) n = eCoeff f n + eCoeff g n := by
  simp [eCoeff, mul_add]

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.generating_identity, D5.S1.Recurrence.Periodic.EulerSignedFrequency.integer_moment. -/
private theorem eCoeff_C_mul (c : ℚ) (f : PowerSeries ℚ) (n : ℕ) :
    eCoeff (C c * f) n = c * eCoeff f n := by
  simp [eCoeff, mul_left_comm]

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.generating_identity, D5.S1.Recurrence.Periodic.EulerSignedFrequency.integer_moment. -/
private theorem eCoeff_exp_pow (u n : ℕ) :
    eCoeff ((exp ℚ) ^ u) n = (u : ℚ) ^ n := by
  rw [exp_pow_eq_rescale_exp]
  simp only [eCoeff, coeff_rescale, coeff_exp]
  change (n.factorial : ℚ) * ((u : ℚ) ^ n * (1 / (n.factorial : ℚ))) = _
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- The defining exponential identity is proved from an integral recurrence. -/
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.branch_equations, D5.S1.Recurrence.Periodic.EulerSignedFrequency.finite_identity, D5.S1.Recurrence.Periodic.EulerSecantBridge.H_product. -/
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

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.finite_identity. -/
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
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.scaled_identity. -/
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

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.branch_equations. -/
private theorem denominator_ne_zero : 1 + (exp ℚ) ^ 2 ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  norm_num at this

/-- Differential identities for the hyperbolic secant and tangent branches. -/
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.complex_correspondence. -/
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

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.integer_moment. -/
private theorem scaled_identity (b L u : ℕ) (hL : Odd L) :
    (1 + (exp ℚ) ^ (u * (2 * L))) * rescale (u : ℚ) (F b) =
      C 2 * ∑ h ∈ range L, C ((-1 : ℚ) ^ h) *
        (exp ℚ) ^ (u * (2 * h + b)) := by
  have h := congrArg (rescale (u : ℚ)) (finite_identity b L hL)
  have he : rescale (u : ℚ) (exp ℚ) = (exp ℚ) ^ u :=
    (exp_pow_eq_rescale_exp u).symm
  simpa only [map_mul, map_add, map_one, map_sum, map_pow, map_neg, map_ofNat,
    he, ← pow_mul] using h

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.integer_moment. -/
private theorem eCoeff_scaled_F (b u j : ℕ) :
    eCoeff (rescale (u : ℚ) (F b)) j = (u : ℚ) ^ j * (A b j : ℚ) := by
  simp only [eCoeff, coeff_rescale]
  rw [mul_left_comm]
  exact congrArg ((u : ℚ) ^ j * ·) (eCoeff_F b j)

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSignedFrequency.scaled_moment. -/
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
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerOddPrimePower.corrected_sum. -/
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

namespace D5.S1.Recurrence.Periodic.EulerUpDownSource

/-- The offset-zero ordinary Euler up/down numbers, not the weighted Entringer diagonal. -/
/- proof_shape: definition; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.ordinarySeries. -/
def E : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => ∑ i : Fin (n + 1), (n.choose i) * E i * E (n + 1 - i.val)
termination_by n => n

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.source_equation, D5.S1.Recurrence.Periodic.EulerUpDownSource.E_succ_le. -/
private theorem E_step (n : ℕ) : E (n + 2) =
    ∑ i ∈ range (n + 1), n.choose i * E i * E (n + 1 - i) := by
  rw [E, Fin.sum_univ_eq_sum_range (fun i => n.choose i * E i * E (n + 1 - i))]

/-- The exponential generating series of the source-normalized natural carrier. -/
/- proof_shape: definition; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.source_equation. -/
noncomputable def ordinarySeries : PowerSeries ℚ := encode (fun n => (E n : ℚ))

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.source_equation, D5.S1.Recurrence.Periodic.EulerUpDownSource.ordinary_coefficient_complex. -/
private theorem eCoeff_ordinary (n : ℕ) :
    eCoeff ordinarySeries n = (E n : ℚ) := eCoeff_encode _ _

/-- The source equation `A'' = A A'`, including its two initial conditions. -/
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.ordinary_riccati, D5.S1.Recurrence.Periodic.EulerTwoPrimary.U_mul_N. -/
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

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.monotone_E. -/
private theorem E_succ_le (n : ℕ) : E n ≤ E (n + 1) := by
  cases n with
  | zero => simp [E]
  | succ n =>
    rw [show n + 1 + 1 = n + 2 by omega, E_step]
    have h := single_le_sum (fun i (hi : i ∈ range (n + 1)) =>
      Nat.zero_le (n.choose i * E i * E (n + 1 - i)))
      (show 0 ∈ range (n + 1) by simp)
    simpa [E] using h

/-- The source recurrence makes the ordinary Euler carrier nondecreasing. -/
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSecantBridge.boundary_values. -/
theorem monotone_E : Monotone E := monotone_nat_of_le_succ E_succ_le

/-- The ordinary secant-plus-tangent series satisfies its Riccati equation. -/
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.N_riccati, D5.S1.Recurrence.Periodic.EulerTwoPrimary.U_mul_N, D5.S1.Recurrence.Periodic.EulerTwoPrimary.branch_derivatives, D5.S1.Recurrence.Periodic.EulerUpDownSource.complex_correspondence. -/
theorem ordinary_riccati :
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

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.complex_correspondence, D5.S1.Recurrence.Periodic.EulerUpDownSource.liftI_derivative. -/
private theorem derivative_map_complex (f : PowerSeries ℚ) :
    PowerSeries.derivative (map (algebraMap ℚ ℂ) f) =
      map (algebraMap ℚ ℂ) (PowerSeries.derivative f) := by
  ext n
  simp [coeff_derivative]

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.liftI_derivative. -/
private theorem derivative_rescale_complex (c : ℂ) (f : PowerSeries ℂ) :
    PowerSeries.derivative (rescale c f) = C c * rescale c (PowerSeries.derivative f) := by
  ext n
  simp only [coeff_derivative, coeff_rescale, coeff_C_mul, pow_succ]
  ring

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.complex_correspondence. -/
private theorem riccati_unique (f g : PowerSeries ℂ)
    (h0 : constantCoeff f = constantCoeff g)
    (hf : 2 * PowerSeries.derivative f = f ^ 2 + 1)
    (hg : 2 * PowerSeries.derivative g = g ^ 2 + 1) : f = g := by
  let c : ℂ := constantCoeff f - 1
  let step (h : PowerSeries ℂ) : PowerSeries ℂ :=
    1 + X * mk (fun n => (((n + 1 : ℂ) * 2)⁻¹) * coeff n ((h + C c) ^ 2 + 1))
  have hstep0 (h : PowerSeries ℂ) (_ : constantCoeff h = 1) :
      constantCoeff (step h) = 1 := by simp [step]
  have hcontract {d : ℕ} {h k : PowerSeries ℂ} (_ : 1 ≤ d)
      (_ : constantCoeff h = 1) (_ : constantCoeff k = 1) (hhk : Agree d h k) :
      Agree (d + 1) (step h) (step k) := by
    have heq : Agree d (h + C c) (k + C c) := by
      intro j hj
      simp only [map_add]
      rw [hhk j hj]
    intro n hn
    cases n with
    | zero => simp [step]
    | succ n =>
      simp only [step, map_add, coeff_one, Nat.add_eq_zero_iff, Nat.one_ne_zero,
        and_false, ite_false, coeff_succ_X_mul, coeff_mk, zero_add]
      rw [agree_pow heq 2 n (by omega)]
  have hfixed (h : PowerSeries ℂ) (hh0 : constantCoeff h = c + 1)
      (hD : 2 * PowerSeries.derivative h = h ^ 2 + 1) :
      h - C c = step (h - C c) := by
    ext n
    cases n with
    | zero => simp [step, coeff_zero_eq_constantCoeff, hh0]
    | succ n =>
      simp only [step, map_sub, map_add, coeff_C, coeff_one, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, ite_false, coeff_succ_X_mul, coeff_mk,
        sub_zero, zero_add, sub_add_cancel]
      have he := congrArg (coeff n) hD
      simp only [coeff_ofNat_mul, coeff_derivative, map_add, coeff_one] at he
      rw [← he]
      have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      field_simp
      <;> ring
  obtain ⟨u, _, _, hu⟩ := exists_unique_fixed step hstep0
    (fun hd h0 k0 hhk => hcontract hd h0 k0 hhk)
  have heF := hu (f - C c) (by simp [c]) (hfixed f (by dsimp [c]; ring) hf)
  have heG := hu (g - C c) (by simp [c, ← h0])
    (hfixed g (by dsimp [c]; rw [← h0]; ring) hg)
  linear_combination heF - heG

/- proof_shape: definition; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.liftI_derivative. -/
private noncomputable def liftI (f : PowerSeries ℚ) : PowerSeries ℂ :=
  rescale Complex.I (map (algebraMap ℚ ℂ) f)

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.complex_correspondence. -/
private theorem liftI_derivative (f : PowerSeries ℚ) :
    PowerSeries.derivative (liftI f) = C Complex.I * liftI (PowerSeries.derivative f) := by
  rw [liftI, derivative_rescale_complex, derivative_map_complex]
  rfl

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.complex_coefficient. -/
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

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.complex_coefficient. -/
private theorem liftI_coefficient (b n : ℕ) :
    (n.factorial : ℂ) * coeff n (liftI (EulerSignedFrequency.F b)) =
      Complex.I ^ n * (EulerSignedFrequency.A b n : ℂ) := by
  have h := congrArg (algebraMap ℚ ℂ)
    (eCoeff_encode (fun j => (EulerSignedFrequency.A b j : ℚ)) n)
  simp only [eCoeff, map_mul, map_natCast, map_intCast] at h
  simp only [liftI, coeff_rescale, coeff_map, EulerSignedFrequency.F]
  rw [mul_left_comm]
  exact congrArg (Complex.I ^ n * ·) h

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.complex_coefficient. -/
private theorem ordinary_coefficient_complex (n : ℕ) :
    (n.factorial : ℂ) * coeff n (map (algebraMap ℚ ℂ) ordinarySeries) = (E n : ℂ) := by
  have h := congrArg (algebraMap ℚ ℂ) (eCoeff_ordinary n)
  simpa only [eCoeff, map_mul, map_natCast, coeff_map] using h

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerUpDownSource.signed_even, D5.S1.Recurrence.Periodic.EulerUpDownSource.signed_odd. -/
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
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerDivisorPropagation.zero_even, D5.S1.Recurrence.Periodic.EulerSecantBridge.even_recurrence. -/
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
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerDivisorPropagation.zero_odd. -/
theorem signed_odd (s : ℕ) :
    (E (2 * s + 1) : ℤ) = (-1 : ℤ) ^ (s + 1) *
      EulerSignedFrequency.A 0 (2 * s + 1) := by
  have h := complex_coefficient (2 * s + 1) (by omega)
  rw [pow_succ, pow_mul, Complex.I_sq] at h
  have he : (-1 : ℂ) ^ s = (((-1 : ℤ) ^ s : ℤ) : ℂ) := by norm_cast
  rw [he] at h
  have hr := congrArg Complex.re h
  simp only [Complex.natCast_re, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.intCast_re,
    Complex.intCast_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, mul_zero, sub_zero, zero_add, add_zero, zero_sub] at hr
  simp only [mul_one] at hr
  have hz : (E (2 * s + 1) : ℤ) =
      -((-1 : ℤ) ^ s * EulerSignedFrequency.A 0 (2 * s + 1)) := by
    exact_mod_cast hr
  rw [pow_succ]
  linear_combination hz

end D5.S1.Recurrence.Periodic.EulerUpDownSource

/-! The existing secant recurrence determines the even ordinary subsequence. -/

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode eCoeff_encode eCoeff_ext)
open D5.S1.Recurrence.Periodic.EulerUpDownSource
open D5.S1.Recurrence.Periodic.EulerSignedFrequency

namespace D5.S1.Recurrence.Periodic.EulerSecantBridge

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSecantBridge.signed_convolution. -/
private theorem sum_even (f : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ range (2 * n + 1), if Even i then f i else 0) =
      ∑ j ∈ range (n + 1), f (2 * j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = (∑ i ∈ range (2 * n + 1), if Even i then f i else 0) +
          f (2 * (n + 1)) := by
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega,
          sum_range_succ, sum_range_succ]
        simp [show Even (2 * n + 1 + 1) from ⟨n + 1, by omega⟩,
          show ¬Even (2 * n + 1) from Nat.not_even_iff_odd.mpr ⟨n, by omega⟩,
          show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
      _ = (∑ j ∈ range (n + 1), f (2 * j)) + f (2 * (n + 1)) := by rw [ih]
      _ = _ := (sum_range_succ _ (n + 1)).symm

/- proof_shape: definition; consumers: D5.S1.Recurrence.Periodic.EulerSecantBridge.H_product. -/
private noncomputable def H : PowerSeries ℚ :=
  encode (fun n => if Even n then 1 else 0)

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSecantBridge.signed_convolution. -/
private theorem H_product : H * F 1 = 1 := by
  have hh : 2 * H = exp ℚ + rescale (-1 : ℚ) (exp ℚ) := by
    apply eCoeff_ext
    intro n
    have hL : eCoeff (2 * H) n = 2 * (if Even n then 1 else 0) := by
      simp only [eCoeff, coeff_ofNat_mul]
      rw [mul_left_comm]
      change 2 * eCoeff H n = _
      rw [H, eCoeff_encode]
    have hR : eCoeff (exp ℚ + rescale (-1 : ℚ) (exp ℚ)) n =
        1 + (-1 : ℚ) ^ n := by
      have hr : eCoeff (rescale (-1 : ℚ) (exp ℚ)) n = (-1 : ℚ) ^ n := by
        simp only [eCoeff, coeff_rescale]
        rw [mul_left_comm]
        change (-1 : ℚ) ^ n * eCoeff (exp ℚ) n = _
        rw [eCoeff_exp, mul_one]
      simp only [eCoeff, map_add, mul_add] at ⊢
      change eCoeff (exp ℚ) n + eCoeff (rescale (-1 : ℚ) (exp ℚ)) n = _
      rw [eCoeff_exp, hr]
    rw [hL, hR]
    by_cases hn : Even n
    · norm_num [hn, hn.neg_one_pow]
    · simp [hn, (Nat.not_even_iff_odd.mp hn).neg_one_pow]
  have he : exp ℚ * rescale (-1 : ℚ) (exp ℚ) = 1 := by
    simpa using (exp_mul_exp_eq_exp_add (1 : ℚ) (-1))
  have hg := generating_identity 1
  norm_num only [pow_one] at hg
  have hexp : exp ℚ ≠ 0 := by
    intro hz
    have := congrArg constantCoeff hz
    norm_num at this
  apply mul_left_cancel₀ hexp
  apply mul_left_cancel₀ (show (2 : PowerSeries ℚ) ≠ 0 by
    intro hz
    have ht := congrArg constantCoeff hz
    rw [map_ofNat constantCoeff 2, map_zero] at ht
    norm_num at ht)
  have hc : C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat C 2
  rw [hc] at hg
  linear_combination (exp ℚ * F 1) * hh + hg + F 1 * he

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSecantBridge.even_recurrence. -/
private theorem signed_convolution (n : ℕ) :
    (∑ j ∈ range (n + 2), ((2 * (n + 1)).choose (2 * j) : ℤ) *
      A 1 (2 * (n + 1 - j))) = 0 := by
  have h := congrArg (fun f => eCoeff f (2 * (n + 1))) H_product
  rw [eCoeff_mul] at h
  have hs : (∑ i ∈ range (2 * (n + 1) + 1),
      ((2 * (n + 1)).choose i : ℚ) * eCoeff H i * eCoeff (F 1) (2 * (n + 1) - i)) =
      ∑ j ∈ range (n + 2), ((2 * (n + 1)).choose (2 * j) : ℚ) *
        (A 1 (2 * (n + 1 - j)) : ℚ) := by
    calc
      _ = ∑ i ∈ range (2 * (n + 1) + 1), if Even i then
          ((2 * (n + 1)).choose i : ℚ) * (A 1 (2 * (n + 1) - i) : ℚ) else 0 := by
        apply sum_congr rfl
        intro i hi
        simp only [H, F, eCoeff_encode]
        split_ifs <;> ring
      _ = _ := by
        rw [sum_even]
        apply sum_congr rfl
        intro j hj
        rw [show 2 * (n + 1) - 2 * j = 2 * (n + 1 - j) by omega]
  rw [hs] at h
  have hz : eCoeff (1 : PowerSeries ℚ) (2 * (n + 1)) = 0 := by
    simp [eCoeff, coeff_one, show 2 * (n + 1) ≠ 0 by omega]
  rw [hz] at h
  exact_mod_cast h

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSecantBridge.secant_bridge. -/
private theorem even_recurrence (n : ℕ) :
    (E (2 * (n + 1)) : ℤ) = ∑ j : Fin (n + 1),
      (-1 : ℤ) ^ (j.val + 2) *
        ((2 * (n + 1)).choose (2 * (j.val + 1)) : ℤ) * (E (2 * (n - j.val)) : ℤ) := by
  have h := signed_convolution n
  rw [sum_range_succ'] at h
  simp only [Nat.mul_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] at h
  rw [signed_even]
  have he : A 1 (2 * (n + 1)) =
      -∑ j ∈ range (n + 1), ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) *
        A 1 (2 * (n - j)) := by
    have hsum : (∑ j ∈ range (n + 1),
        ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * A 1 (2 * (n + 1 - (j + 1)))) =
        ∑ j ∈ range (n + 1), ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) *
          A 1 (2 * (n - j)) := by
      apply sum_congr rfl
      intro j hj
      rw [show n + 1 - (j + 1) = n - j by omega]
    rw [hsum] at h
    linear_combination h
  rw [he, mul_neg, mul_sum,
    Fin.sum_univ_eq_sum_range (fun j => (-1 : ℤ) ^ (j + 2) *
      ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * (E (2 * (n - j)) : ℤ)),
    ← sum_neg_distrib]
  apply sum_congr rfl
  intro j hj
  rw [signed_even]
  have hjn := mem_range.mp hj
  have heven : (-1 : ℤ) ^ (j + 2) * (-1 : ℤ) ^ (n - j) =
      -(-1 : ℤ) ^ (n + 1) := by
    rw [← pow_add, show j + 2 + (n - j) = (n + 1) + 1 by omega, pow_succ]
    ring
  linear_combination -((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) *
    A 1 (2 * (n - j)) * heven

/-- The even subsequence is exactly the repository's existing A000364 carrier. -/
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerSecantBridge.boundary_values. -/
theorem secant_bridge (s : ℕ) :
    (E (2 * s) : ℤ) = SecantNumberPurePeriodRefutation.a s := by
  have hh := SecantNumberPurePeriodRefutation.a_unique
    (fun s => (E (2 * s) : ℤ)) (by simp [E]) even_recurrence
  exact congrFun hh s

/-- The exact source boundary values and the strict bound needed for the particular family. -/
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerDivisorPropagation.divisor_propagation, D5.S1.Recurrence.Periodic.EulerDivisorPropagation.particular, D5.S1.Recurrence.Periodic.EulerDivisorPropagation.two_primary, Reg.D5.S1.Recurrence.Periodic.EulerDivisorPropagation.dependence. -/
theorem boundary_values : E 0 = 1 ∧ E 1 = 1 ∧ E 2 = 1 ∧ E 3 = 2 ∧
    ∀ k : ℕ, 4 ≤ k → 2 < E k := by
  refine ⟨by simp [E], by simp [E], ?_, ?_, ?_⟩
  · norm_num [E, Fin.sum_univ_succ]
  · norm_num [E, Fin.sum_univ_succ]
  · intro k hk
    have he4 : E 4 = 5 := by
      have he := secant_bridge 2
      rw [SecantNumberPurePeriodRefutation.initial_values.2.2.1] at he
      exact_mod_cast he
    have hh := monotone_E hk
    rw [he4] at hh
    omega

end D5.S1.Recurrence.Periodic.EulerSecantBridge

/-! Parity projections of the ordinary Euler exponential series. -/

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode eCoeff_encode eCoeff_ext)
open D5.S1.Recurrence.Periodic.EulerUpDownSource

namespace D5.S1.Recurrence.Periodic.EulerTwoPrimary

/- proof_shape: definition; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.eS. -/
private noncomputable def S : PowerSeries ℚ :=
  encode (fun n => if Even n then (E n : ℚ) else 0)
/- proof_shape: definition; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.eT. -/
private noncomputable def T : PowerSeries ℚ :=
  encode (fun n => if Odd n then (E n : ℚ) else 0)
/- proof_shape: definition; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.N_riccati. -/
private noncomputable def N : PowerSeries ℚ := rescale (-1 : ℚ) ordinarySeries

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.parity_decomposition, D5.S1.Recurrence.Periodic.EulerTwoPrimary.secant_recurrence. -/
private theorem eS (n : ℕ) : eCoeff S n = if Even n then (E n : ℚ) else 0 :=
  eCoeff_encode _ _
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.parity_decomposition, D5.S1.Recurrence.Periodic.EulerTwoPrimary.secant_recurrence, D5.S1.Recurrence.Periodic.EulerTwoPrimary.tangent_recurrence. -/
private theorem eT (n : ℕ) : eCoeff T n = if Odd n then (E n : ℚ) else 0 :=
  eCoeff_encode _ _
/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.parity_decomposition. -/
private theorem eU (n : ℕ) : eCoeff ordinarySeries n = (E n : ℚ) := eCoeff_encode _ _

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.branch_derivatives. -/
private theorem parity_decomposition : ordinarySeries = S + T ∧ N = S - T := by
  constructor <;> apply eCoeff_ext <;> intro n
  · simp only [eCoeff, map_add, mul_add]
    change eCoeff ordinarySeries n = eCoeff S n + eCoeff T n
    rw [eU, eS, eT]
    by_cases hn : Even n
    · simp [hn, Nat.not_odd_iff_even.mpr hn]
    · simp [hn, Nat.not_even_iff_odd.mp hn]
  · have he : eCoeff N n = (-1 : ℚ) ^ n * (E n : ℚ) := by
      simp only [N, eCoeff, coeff_rescale]
      rw [mul_left_comm]
      exact congrArg ((-1 : ℚ) ^ n * ·) (eU n)
    change eCoeff N n = _
    rw [he]
    change _ = (n.factorial : ℚ) * (coeff n S - coeff n T)
    rw [mul_sub]
    change _ = eCoeff S n - eCoeff T n
    rw [eS, eT]
    by_cases hn : Even n
    · simp [hn, Nat.not_odd_iff_even.mpr hn, hn.neg_one_pow]
    · have ho := Nat.not_even_iff_odd.mp hn
      simp [hn, ho, ho.neg_one_pow]

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.U_mul_N, D5.S1.Recurrence.Periodic.EulerTwoPrimary.branch_derivatives. -/
private theorem N_riccati : 2 * PowerSeries.derivative N = -(N ^ 2 + 1) := by
  have hd : PowerSeries.derivative N = -rescale (-1 : ℚ)
      (PowerSeries.derivative ordinarySeries) := by
    ext n
    simp only [N, coeff_derivative, coeff_rescale, map_neg, pow_succ]
    ring
  have hh := congrArg (rescale (-1 : ℚ)) ordinary_riccati
  simp only [map_mul, map_ofNat, map_pow, map_add, map_one] at hh
  rw [hd]
  change _ = -((rescale (-1 : ℚ) ordinarySeries) ^ 2 + 1)
  linear_combination -hh

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.branch_derivatives. -/
private theorem U_mul_N : ordinarySeries * N = 1 := by
  let P := ordinarySeries * N - 1
  let H := C (1 / 2 : ℚ) * (ordinarySeries - N)
  have hd : PowerSeries.derivative P = H * P := by
    dsimp [P, H]
    simp only [map_sub, Derivation.leibniz, derivative_one, sub_zero]
    have hc : (2 : PowerSeries ℚ) * C (1 / 2 : ℚ) = 1 := by
      change C (2 : ℚ) * C (1 / 2 : ℚ) = 1
      rw [← map_mul]
      norm_num
    apply mul_left_cancel₀ (show (2 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hh := congrArg constantCoeff hz
      rw [map_ofNat constantCoeff 2] at hh
      norm_num at hh)
    linear_combination N * ordinary_riccati + ordinarySeries * N_riccati -
      (ordinarySeries - N) * (ordinarySeries * N - 1) * hc
  have hN : constantCoeff N = 1 := by
    rw [← coeff_zero_eq_constantCoeff]
    simp only [N, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff, source_equation.1]
  have hzero : coeff 0 P = coeff 0 (0 : PowerSeries ℚ) := by
    simp only [coeff_zero_eq_constantCoeff, P, map_sub, map_mul, map_one,
      source_equation.1, hN, one_mul, sub_self, map_zero]
  have hp := D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence.linear_ode_unique
    P 0 H hzero hd (by simp)
  dsimp [P] at hp
  linear_combination hp

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.secant_recurrence, D5.S1.Recurrence.Periodic.EulerTwoPrimary.tangent_recurrence. -/
private theorem branch_derivatives :
    PowerSeries.derivative S = S * T ∧ PowerSeries.derivative T = 1 + T ^ 2 := by
  have hu := ordinary_riccati
  have hn := N_riccati
  have hi := U_mul_N
  rw [parity_decomposition.1] at hu
  rw [parity_decomposition.2] at hn
  rw [parity_decomposition.1, parity_decomposition.2] at hi
  simp only [map_add, map_sub] at hu hn
  have htwo : (2 : PowerSeries ℚ) ≠ 0 := by
    intro hz
    have hh := congrArg constantCoeff hz
    rw [map_ofNat constantCoeff 2] at hh
    norm_num at hh
  constructor
  · apply mul_left_cancel₀ (pow_ne_zero 2 htwo)
    linear_combination hu + hn
  · apply mul_left_cancel₀ (pow_ne_zero 2 htwo)
    linear_combination hu - hn + 2 * hi

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.tangent_power. -/
private theorem tangent_recurrence (s : ℕ) (hs : 0 < s) :
    E (2 * s + 1) = ∑ i ∈ range (2 * s + 1),
      if Odd i ∧ Odd (2 * s - i) then
        (2 * s).choose i * E i * E (2 * s - i) else 0 := by
  have h := congrArg (fun f => eCoeff f (2 * s)) branch_derivatives.2
  rw [eCoeff_derivative, eT] at h
  simp only [show Odd (2 * s + 1) from ⟨s, by omega⟩, ite_true] at h
  have h1 : eCoeff (1 : PowerSeries ℚ) (2 * s) = 0 := by
    simp [eCoeff, coeff_one, show 2 * s ≠ 0 by omega]
  have ha : eCoeff (1 + T ^ 2) (2 * s) = eCoeff (T ^ 2) (2 * s) := by
    simp only [eCoeff, map_add, mul_add] at h1 ⊢
    exact add_eq_right.mpr h1
  rw [ha, pow_two, eCoeff_mul] at h
  have hsum : (∑ i ∈ range (2 * s + 1), ((2 * s).choose i : ℚ) *
      eCoeff T i * eCoeff T (2 * s - i)) =
      ((∑ i ∈ range (2 * s + 1), if Odd i ∧ Odd (2 * s - i) then
        (2 * s).choose i * E i * E (2 * s - i) else 0 : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    apply sum_congr rfl
    intro i hi
    rw [eT, eT]
    split_ifs <;> simp_all
  rw [hsum] at h
  exact_mod_cast h

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.tangent_power. -/
private theorem choose_even_odd (s i : ℕ) (hi : Odd i) : 2 ∣ (2 * s).choose i := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * s) (k := i) (p := 2)
  have him : i % 2 = 1 := Nat.odd_iff.mp hi
  apply Nat.dvd_of_mod_eq_zero
  simpa [Nat.ModEq, him] using h

/-- The elementary tangent bound, with all indices including zero. -/
/- proof_shape: content; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.secant_odd, D5.S1.Recurrence.Periodic.EulerDivisorPropagation.two_primary. -/
theorem tangent_power (s : ℕ) : 2 ^ s ∣ E (2 * s + 1) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hs : s = 0
    · subst s
      simp
    rw [tangent_recurrence s (by omega)]
    apply dvd_sum
    intro i hi
    split_ifs with ho
    · obtain ⟨j, hj⟩ := ho.1
      obtain ⟨l, hl⟩ := ho.2
      have hir := mem_range.mp hi
      have hjlt : j < s := by omega
      have hllt : l < s := by omega
      have he : j + l + 1 = s := by omega
      have hjd : 2 ^ j ∣ E i := by simpa [show i = 2 * j + 1 by omega] using ih j hjlt
      have hld : 2 ^ l ∣ E (2 * s - i) := by
        simpa [show 2 * s - i = 2 * l + 1 by omega] using ih l hllt
      have hd := Nat.mul_dvd_mul (Nat.mul_dvd_mul (choose_even_odd s i ho.1) hjd) hld
      convert hd using 1 <;> simp only [← pow_succ', ← pow_add] <;> congr 1 <;> omega
    · exact dvd_zero _

/- proof_shape: bind-only; consumers: D5.S1.Recurrence.Periodic.EulerTwoPrimary.secant_odd. -/
private theorem secant_recurrence (s : ℕ) :
    E (2 * s + 2) = ∑ i ∈ range (2 * s + 2),
      if Even i ∧ Odd (2 * s + 1 - i) then
        (2 * s + 1).choose i * E i * E (2 * s + 1 - i) else 0 := by
  have h := congrArg (fun f => eCoeff f (2 * s + 1)) branch_derivatives.1
  rw [eCoeff_derivative, eS, eCoeff_mul] at h
  simp only [show Even (2 * s + 1 + 1) from ⟨s + 1, by omega⟩, ite_true] at h
  have hsum : (∑ i ∈ range (2 * s + 1 + 1), ((2 * s + 1).choose i : ℚ) *
      eCoeff S i * eCoeff T (2 * s + 1 - i)) =
      ((∑ i ∈ range (2 * s + 2), if Even i ∧ Odd (2 * s + 1 - i) then
        (2 * s + 1).choose i * E i * E (2 * s + 1 - i) else 0 : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    apply sum_congr (by congr 1 <;> omega)
    intro i hi
    rw [eS, eT]
    split_ifs <;> simp_all
  rw [hsum] at h
  exact_mod_cast h

/-- Every even-index ordinary Euler number is odd. -/
/- proof_shape: content; consumers: D5.S1.Recurrence.Periodic.EulerDivisorPropagation.two_primary. -/
theorem secant_odd (s : ℕ) : Odd (E (2 * s)) := by
  induction s with
  | zero => simp [E]
  | succ s ih =>
    have hrec := secant_recurrence s
    have hmod : E (2 * s + 2) % 2 = E (2 * s) % 2 := by
      rw [hrec, Finset.sum_nat_mod]
      have hsum : (∑ i ∈ range (2 * s + 2),
          (if Even i ∧ Odd (2 * s + 1 - i) then
            (2 * s + 1).choose i * E i * E (2 * s + 1 - i) else 0) % 2) =
          ((2 * s + 1) * E (2 * s)) % 2 := by
        rw [sum_eq_single (2 * s)]
        · simp [show Even (2 * s) from ⟨s, by omega⟩,
            show 2 * s + 1 - 2 * s = 1 by omega, E, Nat.choose_symm_of_eq_add]
        · intro i hi hne
          split_ifs with ho
          · obtain ⟨l, hl⟩ := ho.2
            have hlpos : 0 < l := by omega
            have hd : 2 ∣ E (2 * s + 1 - i) := by
              have h := tangent_power l
              have ht : 2 ∣ 2 ^ l := dvd_pow_self 2 (by omega : l ≠ 0)
              exact ht.trans (by simpa [show 2 * s + 1 - i = 2 * l + 1 by omega] using h)
            exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hd _)
          · simp
        · intro hn
          exact False.elim (hn (by simp))
      rw [hsum, Nat.mul_mod]
      simp
    apply Nat.odd_iff.mpr
    rw [show 2 * (s + 1) = 2 * s + 2 by omega, hmod]
    exact Nat.odd_iff.mp ih

end D5.S1.Recurrence.Periodic.EulerTwoPrimary

/- GID: D5/S1/Recurrence/Periodic/EulerUpDownSource
   generality: G
   mirror-B: D5/B/S1/Recurrence/Periodic/EulerUpDownSource
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The ordinary A000111 carrier with its exact source recurrence and differential equation. -/

/-
proof_shape: signed_even and signed_odd are content after same-delivery inlining of
riccati_unique's coefficient induction. A, F, E and ordinarySeries are definitions.
The remaining public theorems are bind-only auxiliary declarations, with consumers:
generating_identity -> finite_identity, branch_equations and EulerSecantBridge.H_product;
finite_identity -> scaled_identity; branch_equations -> complex_correspondence;
scaled_moment -> EulerOddPrimePower.corrected_sum; source_equation -> ordinary_riccati;
monotone_E -> EulerSecantBridge.boundary_values; ordinary_riccati -> complex_correspondence
and EulerTwoPrimary.N_riccati.
escape_witness: signed_even and signed_odd, consumed by EulerSecantBridge.even_recurrence
and EulerDivisorPropagation.zero_even/zero_odd on the live proof paths.
admission_basis: escape-witness. The external resolution basis is reserved for the two
final source assertions of #31280; this supporting module has no resolution claim.
Frozen suppliers: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode, eCoeff_encode,
eCoeff_ext, constantCoeff_encode) and its IntegralEGFComposition coefficient interface
(eCoeff, eCoeff_zero, eCoeff_derivative, eCoeff_mul). Other imports are pinned Mathlib.
Private theorem consumers: eCoeff_F/eCoeff_add/eCoeff_C_mul/eCoeff_exp_pow -> generating_identity;
odd_geometric -> finite_identity; denominator_ne_zero -> branch_equations;
scaled_identity/eCoeff_scaled_F -> integer_moment -> scaled_moment;
E_step -> source_equation; eCoeff_ordinary -> source_equation and ordinary_coefficient_complex;
E_succ_le -> monotone_E; derivative_map_complex/derivative_rescale_complex -> liftI_derivative;
riccati_unique -> complex_correspondence; liftI_derivative/complex_correspondence/
liftI_coefficient/ordinary_coefficient_complex/complex_coefficient -> signed_even/signed_odd.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/31291.
-/

import D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic

/-! Ordinary Euler up/down numbers use the positive recurrence in OEIS A000111. -/

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode eCoeff_encode eCoeff_ext)

/-! Integral coefficients of two signed Euler branches and their finite frequency sums. -/

set_option maxRecDepth 2048

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

/-- The source recurrence makes the ordinary Euler carrier nondecreasing. -/
theorem monotone_E : Monotone E := monotone_nat_of_le_succ E_succ_le

/-- The ordinary secant-plus-tangent series satisfies its Riccati equation. -/
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
  simp only [eCoeff, map_mul, map_natCast, map_intCast] at h
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

/- GID: D5/S1/Recurrence/Periodic/EulerTwoPrimary
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/EulerTwoPrimary
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Tangent divisibility and secant parity for the ordinary Euler carrier. -/

/-
proof_shape: tangent_power and secant_odd are content proofs. tangent_power supplies the
two-primary tangent valuation and secant_odd supplies the even-index parity needed to force
an odd source index.
escape_witness: tangent_power and secant_odd, both consumed by EulerDivisorPropagation.two_primary.
admission_basis: escape-witness. The external resolution basis of #31280 belongs only to
the final source assertions; this supporting module carries no resolution claim.
Frozen suppliers: D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence
(linear_ode_unique), IntegralEGFComposition's coefficient interface and
QuarticEGFFixedPoint's encoding interface. EulerUpDownSource is a same-delivery dependency.
Private theorem consumers: parity_decomposition/N_riccati/U_mul_N/branch_derivatives/
tangent_recurrence/choose_even_odd/secant_recurrence -> tangent_power/secant_odd.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/31291.
-/

import D5.S1.Recurrence.Periodic.EulerUpDownSource
import D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence
import Mathlib.Data.Nat.Choose.Lucas

/-! Parity projections of the ordinary Euler exponential series. -/

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (encode eCoeff_encode eCoeff_ext)
open D5.S1.Recurrence.Periodic.EulerUpDownSource

namespace D5.S1.Recurrence.Periodic.EulerTwoPrimary

private noncomputable def S : PowerSeries ℚ :=
  encode (fun n => if Even n then (E n : ℚ) else 0)
private noncomputable def T : PowerSeries ℚ :=
  encode (fun n => if Odd n then (E n : ℚ) else 0)
private noncomputable def N : PowerSeries ℚ := rescale (-1 : ℚ) ordinarySeries

private theorem eS (n : ℕ) : eCoeff S n = if Even n then (E n : ℚ) else 0 :=
  eCoeff_encode _ _
private theorem eT (n : ℕ) : eCoeff T n = if Odd n then (E n : ℚ) else 0 :=
  eCoeff_encode _ _
private theorem eU (n : ℕ) : eCoeff ordinarySeries n = (E n : ℚ) := eCoeff_encode _ _

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

private theorem choose_even_odd (s i : ℕ) (hi : Odd i) : 2 ∣ (2 * s).choose i := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 * s) (k := i) (p := 2)
  have him : i % 2 = 1 := Nat.odd_iff.mp hi
  apply Nat.dvd_of_mod_eq_zero
  simpa [Nat.ModEq, him] using h

/-- The elementary tangent bound, with all indices including zero. -/
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

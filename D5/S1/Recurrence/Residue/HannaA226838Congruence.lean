/- GID: D5/S1/Recurrence/Residue/HannaA226838Congruence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/HannaA226838Congruence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The original square-exponent rational EGF congruence modulo six. -/

import Batteries.Tactic.OpenPrivate
import D5.S1.Recurrence.Residue.QuarticEGFModFour
import D5.S3.Arith.Congruence.BourasA363347PrimeMultiplicity

open PowerSeries Finset
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (identity)
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open private composition_identity_right from
  D5.S1.Recurrence.Residue.QuarticEGFModFour
open private pow_dvd_factorial_mul from
  D5.S3.Arith.Congruence.BourasA363347PrimeMultiplicity

namespace D5.S1.Recurrence.Residue.HannaA226838Congruence

/-- Coefficientwise formal sum of X^(m²)/m^m over positive m. -/
noncomputable def H : PowerSeries ℚ := PowerSeries.mk fun n =>
  ∑ᶠ m : ℕ, if 0 < m then
    coeff n (monomial (m ^ 2) (1 / (m : ℚ) ^ m)) else 0

/-- The formal exponential of the exact rational source series. -/
noncomputable def A : PowerSeries ℚ := (PowerSeries.exp ℚ).subst H

/-- Factorial ratios on the square support, zero away from that support. -/
def innerIntegral (n : ℕ) : ℕ :=
  ∑ m ∈ range (n + 1), if 0 < m ∧ m ^ 2 = n then
    n.factorial / m ^ m else 0

private theorem le_square (m : ℕ) : m ≤ m ^ 2 := by
  nlinarith [Nat.mul_self_le_mul_self (show 0 ≤ m by omega)]

private theorem power_dvd_square_factorial {m : ℕ} (hm : 0 < m) :
    m ^ m ∣ (m ^ 2).factorial := by
  simpa [pow_two] using pow_dvd_factorial_mul m m hm

private theorem six_power_dvd_square_factorial {m : ℕ} (hm : 2 ≤ m) :
    6 * m ^ m ∣ (m ^ 2).factorial := by
  by_cases h2 : m = 2
  · subst m; norm_num [Nat.factorial]
  by_cases h3 : m = 3
  · subst m; norm_num [Nat.factorial]
  have hm4 : 4 ≤ m := by omega
  have h6 : 6 ∣ (m - 1).factorial :=
    (by decide : 6 ∣ Nat.factorial 3).trans (Nat.factorial_dvd_factorial (by omega))
  have h6m : 6 * m ∣ m.factorial := by
    have h := Nat.mul_dvd_mul_left m h6
    rw [show m = (m - 1) + 1 by omega, Nat.factorial_succ]
    simpa [Nat.mul_comm] using h
  have hpow : (6 * m) ^ m ∣ m.factorial ^ m := pow_dvd_pow_of_dvd h6m m
  have hp : 6 * m ^ m ∣ (6 * m) ^ m := by
    rw [mul_pow]
    exact mul_dvd_mul (dvd_pow_self 6 (by omega : m ≠ 0)) (dvd_refl _)
  have hprod : m.factorial ^ m ∣ (m ^ 2).factorial := by
    simpa [pow_two, Nat.mul_comm] using
      Nat.prod_factorial_dvd_factorial_sum (range m) (fun _ : ℕ => m)
  exact hp.trans (hpow.trans hprod)

private theorem factorial_ratio {m n : ℕ} (hm : 0 < m) (hmn : m ^ 2 = n) :
    (n.factorial : ℚ) * (1 / (m : ℚ) ^ m) =
      (n.factorial / m ^ m : ℕ) := by
  have hd : m ^ m ∣ n.factorial := hmn ▸ power_dvd_square_factorial hm
  have hz : ((m ^ m : ℕ) : ℚ) ≠ 0 := by positivity
  rw [Nat.cast_div hd hz]
  push_cast
  ring

private theorem coeff_H (n : ℕ) : coeff n H =
    ∑ m ∈ range (n + 1), if 0 < m ∧ m ^ 2 = n then
      (1 / (m : ℚ) ^ m) else 0 := by
  classical
  rw [H, coeff_mk]
  have hs : Function.support (fun m : ℕ => if 0 < m then
      coeff n (monomial (m ^ 2) (1 / (m : ℚ) ^ m)) else 0) ⊆
      (range (n + 1) : Set ℕ) := by
    intro m hm
    by_contra hn
    have hmn : n < m := by simpa using hn
    have hne : n ≠ m ^ 2 := by have := le_square m; omega
    exact hm (by simp [coeff_monomial, hne])
  rw [finsum_eq_sum_of_support_subset _ hs]
  apply sum_congr rfl
  intro m _
  by_cases hm : 0 < m <;> simp [hm, coeff_monomial, eq_comm]

private theorem eCoeff_H (n : ℕ) : eCoeff H n = (innerIntegral n : ℚ) := by
  classical
  simp only [eCoeff, coeff_H, innerIntegral, Nat.cast_sum, mul_sum]
  apply sum_congr rfl
  intro m hm
  split_ifs with h
  · exact factorial_ratio h.1 h.2
  · simp

private theorem H_zero : constantCoeff H = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_H]
  simp

private theorem inner_mod_six (n : ℕ) :
    (innerIntegral n : ZMod 6) = if n = 1 then 1 else 0 := by
  classical
  by_cases hn : n = 1
  · subst n
    norm_num [innerIntegral, sum_range_succ]
  · rw [ite_eq_right hn]
    simp only [innerIntegral, Nat.cast_sum]
    apply sum_eq_zero
    intro m hm
    by_cases hc : 0 < m ∧ m ^ 2 = n
    · rw [ite_eq_left hc]
      have hm2 : 2 ≤ m := by
        have hm1 : m ≠ 1 := by
          intro he
          subst m
          norm_num at hc
          omega
        omega
      apply (ZMod.natCast_eq_zero_iff _ 6).2
      rw [← hc.2]
      obtain ⟨k, hk⟩ := six_power_dvd_square_factorial hm2
      rw [hk]
      have hz : 0 < m ^ m := pow_pos hc.1 _
      rw [show 6 * m ^ m * k = (6 * k) * m ^ m by ring,
        Nat.mul_div_cancel _ hz]
      exact dvd_mul_right 6 k
    · simp [hc]

private theorem composition_unit_mod_six (n : ℕ) :
    composition (fun _ => (1 : ZMod 6)) (fun j => if j = 1 then 1 else 0) n = 1 := by
  have h := congrFun (composition_identity_right (fun _ => 1)) n
  have hm := congrArg (fun z : ℤ => (z : ZMod 6)) h
  change (Int.castRingHom (ZMod 6)) (composition (fun _ => 1) identity n) = _ at hm
  rw [composition_map] at hm
  simpa [identity] using hm

/-- For every index, including zero, the original rational EGF coefficient
has an integral residue witness modulo six. -/
theorem result (n : ℕ) : ∃ k : ℤ,
    (n.factorial : ℚ) * coeff n A = 1 + 6 * (k : ℚ) := by
  let z : ℕ → ℤ := fun j => (innerIntegral j : ℤ)
  have he (j : ℕ) : eCoeff H j = (z j : ℚ) := by simpa [z] using eCoeff_H j
  have hc : eCoeff A n = ((composition (fun _ => (1 : ℤ)) z n : ℤ) : ℚ) := by
    rw [A, eCoeff_composition _ _ H_zero]
    rw [funext eCoeff_exp, funext he]
    exact (composition_map (Int.castRingHom ℚ) (fun _ => 1) z n).symm
  have hm : ((composition (fun _ => (1 : ℤ)) z n : ℤ) : ZMod 6) = 1 := by
    have hmap := composition_map (Int.castRingHom (ZMod 6)) (fun _ => 1) z n
    change ((composition (fun _ => (1 : ℤ)) z n : ℤ) : ZMod 6) = _ at hmap
    rw [hmap]
    have hz : (fun j => (z j : ZMod 6)) = (fun j => if j = 1 then 1 else 0) := by
      funext j
      simpa [z] using inner_mod_six j
    change composition (fun _ => (1 : ZMod 6)) (fun j => (z j : ZMod 6)) n = 1
    rw [hz]
    exact composition_unit_mod_six n
  have hd : (6 : ℤ) ∣ composition (fun _ => (1 : ℤ)) z n - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 6).1
    simp only [Int.cast_sub, Int.cast_one, hm, sub_self]
  obtain ⟨k, hk⟩ := hd
  refine ⟨k, ?_⟩
  change eCoeff A n = _
  rw [hc]
  have heq : composition (fun _ => (1 : ℤ)) z n = 1 + 6 * k := by linarith
  exact_mod_cast heq

#print axioms result
#check result

end D5.S1.Recurrence.Residue.HannaA226838Congruence

/- GID: D5/S1/Recurrence/Residue/HannaA226839Congruence
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/HannaA226839Congruence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The original triangular-exponent rational EGF congruence modulo three. -/

import Batteries.Tactic.OpenPrivate
import D5.S1.Recurrence.Residue.QuarticEGFModFour

/-! The all-index congruence for the rational formal EGF in OEIS A226839. -/

open PowerSeries Finset
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint (identity)
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open private composition_identity_right from
  D5.S1.Recurrence.Residue.QuarticEGFModFour

namespace D5.S1.Recurrence.Residue.HannaA226839Congruence

/-- The exponent in the original OEIS A226839 inner series. -/
def triangular (m : ℕ) : ℕ := m * (m + 1) / 2

/-- Coefficientwise formal sum over the positive indices of the source series. -/
noncomputable def H : PowerSeries ℚ := PowerSeries.mk fun n =>
  ∑ᶠ m : ℕ, if 0 < m then
    coeff n (monomial (triangular m) (1 / (m.factorial : ℚ))) else 0

/-- Formal exponential of the original rational inner series. -/
noncomputable def A : PowerSeries ℚ := (PowerSeries.exp ℚ).subst H

/-- Integral factorial ratios at the source exponents, with zero elsewhere. -/
def innerIntegral (n : ℕ) : ℕ :=
  ∑ m ∈ range (n + 1), if 0 < m ∧ triangular m = n then
    (m + 1).ascFactorial (n - m) else 0

private theorem le_triangular (m : ℕ) : m ≤ triangular m := by
  unfold triangular
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  by_cases hm : m = 0
  · subst m; simp
  · have hp : 1 ≤ m := by omega
    nlinarith [Nat.mul_le_mul_left m hp]

private theorem three_le_gap {m : ℕ} (hm : 3 ≤ m) : m + 3 ≤ triangular m := by
  unfold triangular
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  nlinarith

private theorem factorial_ratio (m n : ℕ) (hmn : m ≤ n) :
    (n.factorial : ℚ) * (1 / (m.factorial : ℚ)) =
      ((m + 1).ascFactorial (n - m) : ℚ) := by
  have h := Nat.factorial_mul_ascFactorial m (n - m)
  rw [Nat.add_sub_of_le hmn] at h
  have hq : (m.factorial : ℚ) * ((m + 1).ascFactorial (n - m) : ℚ) = n.factorial := by
    exact_mod_cast h
  have hn : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp
  nlinarith [hq]

private theorem coeff_H (n : ℕ) : coeff n H =
    ∑ m ∈ range (n + 1), if 0 < m ∧ triangular m = n then
      (1 / (m.factorial : ℚ)) else 0 := by
  classical
  rw [H, coeff_mk]
  have hs : Function.support (fun m : ℕ => if 0 < m then
      coeff n (monomial (triangular m) (1 / (m.factorial : ℚ))) else 0) ⊆
      (range (n + 1) : Set ℕ) := by
    intro m hm
    by_contra hn
    have hmn : n < m := by simpa using hn
    have hne : n ≠ triangular m := by have := le_triangular m; omega
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
  · exact factorial_ratio m n (by simpa [← h.2] using le_triangular m)
  · simp

private theorem H_zero : constantCoeff H = 0 := by
  rw [← coeff_zero_eq_constantCoeff, coeff_H]
  simp

private theorem ratio_dvd_three {m : ℕ} (hm : 2 ≤ m) :
    3 ∣ (m + 1).ascFactorial (triangular m - m) := by
  by_cases h2 : m = 2
  · subst m
    norm_num [triangular, Nat.ascFactorial]
  · have hgap : 3 ≤ triangular m - m := by have := three_le_gap (m := m) (by omega); omega
    have hf := Nat.factorial_dvd_ascFactorial (m + 1) (triangular m - m)
    exact dvd_trans (dvd_trans (by decide : 3 ∣ Nat.factorial 3)
      (Nat.factorial_dvd_factorial hgap)) hf

private theorem inner_mod_three (n : ℕ) :
    (innerIntegral n : ZMod 3) = if n = 1 then 1 else 0 := by
  classical
  by_cases hn : n = 1
  · subst n
    norm_num [innerIntegral, triangular, sum_range_succ, Nat.ascFactorial]
  · rw [ite_eq_right hn]
    simp only [innerIntegral, Nat.cast_sum]
    apply sum_eq_zero
    intro m hm
    by_cases hc : 0 < m ∧ triangular m = n
    · rw [ite_eq_left hc]
      have hm2 : 2 ≤ m := by
        have hm1 : m ≠ 1 := by
          intro he
          subst m
          norm_num [triangular] at hc
          omega
        omega
      apply (ZMod.natCast_eq_zero_iff _ 3).2
      rw [← hc.2]
      exact ratio_dvd_three hm2
    · simp [hc]

private theorem composition_unit_mod_three (n : ℕ) :
    composition (fun _ => (1 : ZMod 3)) (fun j => if j = 1 then 1 else 0) n = 1 := by
  have h := congrFun (composition_identity_right (fun _ => 1)) n
  have hm := congrArg (fun z : ℤ => (z : ZMod 3)) h
  change (Int.castRingHom (ZMod 3)) (composition (fun _ => 1) identity n) = _ at hm
  rw [composition_map] at hm
  simpa [identity] using hm

/-- Every factorial-normalized rational coefficient of the original formal EGF
is an integer congruent to one modulo three, including the constant term. -/
theorem result (n : ℕ) : ∃ k : ℤ,
    (n.factorial : ℚ) * coeff n A = 1 + 3 * (k : ℚ) := by
  let z : ℕ → ℤ := fun j => (innerIntegral j : ℤ)
  have he (j : ℕ) : eCoeff H j = (z j : ℚ) := by simpa [z] using eCoeff_H j
  have hc : eCoeff A n = ((composition (fun _ => (1 : ℤ)) z n : ℤ) : ℚ) := by
    rw [A, eCoeff_composition _ _ H_zero]
    rw [funext eCoeff_exp, funext he]
    exact (composition_map (Int.castRingHom ℚ) (fun _ => 1) z n).symm
  have hm : ((composition (fun _ => (1 : ℤ)) z n : ℤ) : ZMod 3) = 1 := by
    have hmap := composition_map (Int.castRingHom (ZMod 3)) (fun _ => 1) z n
    change ((composition (fun _ => (1 : ℤ)) z n : ℤ) : ZMod 3) = _ at hmap
    rw [hmap]
    have hz : (fun j => (z j : ZMod 3)) = (fun j => if j = 1 then 1 else 0) := by
      funext j
      simpa [z] using inner_mod_three j
    change composition (fun _ => (1 : ZMod 3)) (fun j => (z j : ZMod 3)) n = 1
    rw [hz]
    exact composition_unit_mod_three n
  have hd : (3 : ℤ) ∣ composition (fun _ => (1 : ℤ)) z n - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1
    simp only [Int.cast_sub, Int.cast_one, hm, sub_self]
  obtain ⟨k, hk⟩ := hd
  refine ⟨k, ?_⟩
  change eCoeff A n = _
  rw [hc]
  have heq : composition (fun _ => (1 : ℤ)) z n = 1 + 3 * k := by linarith
  exact_mod_cast heq

#print axioms result
#check result

end D5.S1.Recurrence.Residue.HannaA226839Congruence

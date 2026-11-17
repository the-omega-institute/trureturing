/- GID: D5/S1/Recurrence/BalaTrinomialCoefficientIdentity
   generality: G
   mirror-B: D5/B/S1/Recurrence/BalaTrinomialCoefficientIdentity
   mirror-E: none(waiver:unbounded-symbolic-identity)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Binomial, mathlib/module/Mathlib.RingTheory.PowerSeries.Inverse, mathlib/module/Mathlib.RingTheory.PowerSeries.Substitution, mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A rational coefficient identity with an inclusive finite binomial sum. -/

import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic
import D5.S1.Recurrence.Invariants.CompositionalIterateCongruence
import D5.S1.Recurrence.Invariants.MatharA000159Recurrence

namespace D5.S1.Recurrence.BalaTrinomialCoefficientIdentity
open PowerSeries
open D5.S1.Recurrence.Invariants.CompositionalIterateCongruence (mobius mobius_zero)
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- The source quotient is formed independently of the proposed finite sum. -/
def source (n : ℕ) : PowerSeries ℚ :=
  (1 + X + X ^ 2) ^ (3 * n) * ((1 + X) ^ (2 * n))⁻¹

private def geometric : PowerSeries ℚ := (invOneSubPow ℚ 1).val

private theorem mobius_one_eq_geometric : mobius (1 : ℚ) = X * geometric := by
  rw [mobius, rescale_one, RingHom.id_apply]
  have h : (mk 1 : PowerSeries ℚ) = geometric := by
    rw [geometric, invOneSubPow_val_succ_eq_mk_add_choose]
    ext i
    simp
  rw [h]

private theorem geometric_power (k : ℕ) :
    geometric ^ k = (invOneSubPow ℚ k).val := by
  rw [geometric, invOneSubPow_eq_inv_one_sub_pow, invOneSubPow_eq_inv_one_sub_pow]
  simp

private theorem mobius_coefficient (f : PowerSeries ℚ) (n : ℕ) (hn : 0 < n) :
    coeff n ((1-X)^(n-1) * f.subst (mobius (1 : ℚ))) = coeff n f := by
  classical
  rw [mobius_one_eq_geometric,
    D5.S1.Recurrence.Invariants.MatharA000159Recurrence.prefactor_subst_coeff,
    ← mobius_one_eq_geometric]
  rw [Finset.sum_eq_single n]
  · rw [mobius_one_eq_geometric, mul_pow]
    rw [show (1-X : PowerSeries ℚ)^(n-1) * (X^n * geometric^n) =
      X^n * ((1-X)^(n-1) * geometric^n) by ring]
    simp [coeff_X_pow_mul', geometric, invOneSubPow_val_succ_eq_mk_add_choose]
  · intro j hj hjn
    have hjn' : j < n := by have := Finset.mem_range.mp hj; omega
    have he : n-1 = (n-1-j)+j := by omega
    have hp : (1-X : PowerSeries ℚ)^(n-1) * geometric^j = (1-X)^(n-1-j) := by
      rw [geometric_power]
      nth_rw 1 [he]
      rw [one_sub_pow_add_mul_invOneSubPow_val_eq_one_sub_pow]
    have ht : (1-X : PowerSeries ℚ)^(n-1) * mobius (1 : ℚ) ^ j =
        X^j * (1-X)^(n-1-j) := by
      rw [mobius_one_eq_geometric, mul_pow]
      calc
        _ = X^j * ((1-X)^(n-1) * geometric^j) := by ring
        _ = _ := by rw [hp]
    rw [ht, coeff_X_pow_mul', if_pos (by omega)]
    have hz : coeff (n-j) ((1-X : PowerSeries ℚ)^(n-1-j)) = 0 := by
      have hpoly : ((1-X : PowerSeries ℚ)^(n-1-j)) =
          (((1-Polynomial.X : Polynomial ℚ)^(n-1-j) : Polynomial ℚ) : PowerSeries ℚ) := by simp
      rw [hpoly, Polynomial.coeff_coe]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      exact lt_of_le_of_lt (Polynomial.natDegree_pow_le.trans
        (Nat.mul_le_mul_left _ (by
          calc
            (1-Polynomial.X : Polynomial ℚ).natDegree ≤
                max (1 : Polynomial ℚ).natDegree Polynomial.X.natDegree := Polynomial.natDegree_sub_le _ _
            _ ≤ 1 := by simp))) (by omega)
    simp [hz]
  · simp

private theorem geometric_cancel : (1-X : PowerSeries ℚ) * geometric = 1 := by
  change (1-X : PowerSeries ℚ) * (invOneSubPow ℚ 1).val = 1
  simpa only [invOneSubPow_inv_eq_one_sub_pow, pow_one] using
    (invOneSubPow ℚ 1).inv_val

private theorem cancel_powers (a b : ℕ) :
    (1-X : PowerSeries ℚ)^a * geometric^(a+b) = geometric^b := by
  simpa only [geometric_power, Nat.add_comm] using
    (one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ b a)

private theorem source_transform (n : ℕ) (hn : 0 < n) :
    (1-X : PowerSeries ℚ)^(n-1) * (source n).subst (mobius (1 : ℚ)) =
      (1 + X^2 * geometric)^(3*n) * geometric := by
  let hs : HasSubst (mobius (1 : ℚ)) := .of_constantCoeff_zero' (mobius_zero (1 : ℚ))
  have hone : (1 : PowerSeries ℚ).subst (mobius (1 : ℚ)) = 1 := by
    rw [← coe_substAlgHom hs, map_one]
  have ha : 1 + mobius (1 : ℚ) = geometric := by
    have h := geometric_cancel
    rw [mobius_one_eq_geometric]
    linear_combination -h
  have ht : 1 + mobius (1 : ℚ) + mobius (1 : ℚ) ^ 2 =
      (1 + X^2 * geometric) * geometric := by
    rw [ha, mobius_one_eq_geometric]
    ring
  have hsden : (((1+X : PowerSeries ℚ)^(2*n))⁻¹).subst (mobius (1 : ℚ)) = (1-X)^(2*n) := by
    have h := congrArg (substAlgHom hs)
      (PowerSeries.mul_inv_cancel ((1+X : PowerSeries ℚ)^(2*n)) (by simp))
    have h' : geometric^(2*n) * (((1+X : PowerSeries ℚ)^(2*n))⁻¹).subst (mobius (1 : ℚ)) = 1 := by
      simpa only [coe_substAlgHom, subst_mul hs, subst_pow hs, subst_add hs,
        subst_X hs, hone, ha] using h
    have hc : (1-X : PowerSeries ℚ)^(2*n) * geometric^(2*n) = 1 := by
      rw [← mul_pow, geometric_cancel, one_pow]
    calc
      _ = 1 * (((1+X : PowerSeries ℚ)^(2*n))⁻¹).subst (mobius (1 : ℚ)) := by simp
      _ = ((1-X)^(2*n) * geometric^(2*n)) *
          (((1+X : PowerSeries ℚ)^(2*n))⁻¹).subst (mobius (1 : ℚ)) := by rw [hc]
      _ = _ := by rw [mul_assoc, h', mul_one]
  rw [source, subst_mul hs, subst_pow hs, subst_add hs, subst_add hs,
    subst_pow hs, subst_X hs, hone, ht, hsden, mul_pow]
  have he : n-1+2*n = 3*n-1 := by omega
  calc
    _ = (1+X^2*geometric)^(3*n) *
        ((1-X)^(n-1+2*n) * geometric^(3*n)) := by rw [pow_add]; ring
    _ = _ := by
      rw [he]
      have hc := cancel_powers (3*n-1) 1
      rw [show 3*n-1+1 = 3*n by omega, pow_one] at hc
      rw [hc]

private theorem positive_coefficient (n : ℕ) :
    coeff n ((1+X^2*geometric : PowerSeries ℚ)^(3*n) * geometric) =
      ∑ k ∈ Finset.range (n/2+1), ((3*n).choose k : ℚ) * ((n-k).choose k : ℚ) := by
  classical
  rw [show (1+X^2*geometric : PowerSeries ℚ) = X^2*geometric+1 by ring,
    add_pow, Finset.sum_mul, map_sum]
  have term (k : ℕ) :
      coeff n (((X^2*geometric)^k * (1 : PowerSeries ℚ)^(3*n-k) *
        ((3*n).choose k : PowerSeries ℚ)) * geometric) =
      if 2*k ≤ n then ((3*n).choose k : ℚ) * ((n-k).choose k : ℚ) else 0 := by
    have hp : (((X^2*geometric)^k * (1 : PowerSeries ℚ)^(3*n-k) *
        ((3*n).choose k : PowerSeries ℚ)) * geometric) =
        C ((3*n).choose k : ℚ) * (X^(2*k) * geometric^(k+1)) := by
      simp only [one_pow, mul_one, mul_pow, ← pow_mul, pow_succ]
      rw [show ((3*n).choose k : PowerSeries ℚ) = C ((3*n).choose k : ℚ) by simp]
      ring
    rw [hp, coeff_C_mul, coeff_X_pow_mul']
    split_ifs with hk
    · rw [geometric_power, invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk]
      rw [show k+(n-2*k) = n-k by omega]
    · simp
  simp_rw [term]
  symm
  calc
    _ = ∑ k ∈ Finset.range (n/2+1),
        if 2*k ≤ n then ((3*n).choose k : ℚ) * ((n-k).choose k : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (by have := Finset.mem_range.mp hk; omega)]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega : n/2+1 ≤ 3*n+1))
      intro k hk hnot
      have hb : n/2+1 ≤ k := by simpa only [Finset.mem_range, not_lt] using hnot
      have hh : ¬ 2*k ≤ n := by omega
      rw [if_neg hh]

/-- The full finite-binomial identity, with no lower bound on n. -/
theorem result (n : ℕ) :
    coeff n (source n) =
      (∑ k ∈ Finset.range (n / 2 + 1), (3*n).choose k * (n-k).choose k : ℕ) := by
  by_cases hn : n = 0
  · subst n
    simp [source]
  · rw [← mobius_coefficient (source n) n (by omega), source_transform n (by omega),
      positive_coefficient]
    push_cast
    rfl

end
end D5.S1.Recurrence.BalaTrinomialCoefficientIdentity

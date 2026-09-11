/- GID: D5/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/SquareCubeSubstitutionOddIndexParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Binomial parity descent proves Hanna's odd-index conjecture for A389472. -/

import Mathlib.RingTheory.PowerSeries.Substitution

open PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Parity.SquareCubeSubstitutionOddIndexParity

private noncomputable def q : PowerSeries ℤ := X ^ 2 + X ^ 3

private theorem q_factor : q = X ^ 2 * (1 + X) := by
  dsimp [q]
  ring

private theorem q_zero : constantCoeff q = 0 := by simp [q]

private theorem coeff_q_pow (d k : ℕ) :
    coeff d (q ^ k) = if 2 * k ≤ d then (k.choose (d - 2 * k) : ℤ) else 0 := by
  have hp (j : ℕ) : coeff j ((1 + X : PowerSeries ℤ) ^ k) = (k.choose j : ℤ) := by
    have h := Polynomial.coeff_one_add_X_pow ℤ k j
    rw [← Polynomial.coeff_coe] at h
    simpa using h
  rw [q_factor, mul_pow, ← pow_mul, coeff_X_pow_mul']
  simp only [hp]

private theorem coeff_subst_cut (B : PowerSeries ℤ) (d N : ℕ) (h : d < 2 * N) :
    coeff d (B.subst q) = ∑ k : Fin N, coeff k B * coeff d (q ^ (k : ℕ)) := by
  rw [coeff_subst' (.of_constantCoeff_zero q_zero)]
  simp only [smul_eq_mul]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N)]
  · exact (Fin.sum_univ_eq_sum_range _ N).symm
  · intro k hk
    by_contra hnot
    have hNk : N ≤ k := by simpa using hnot
    exact hk (by dsimp; rw [coeff_q_pow, if_neg (by omega), mul_zero])

noncomputable def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => ∑ k : Fin (n + 3), a k * coeff (n + 5) (q ^ (k : ℕ))
termination_by n => n
decreasing_by exact k.isLt

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem a_step (n : ℕ) (hn : 3 ≤ n) :
    a n = ∑ k : Fin n, a k * coeff (n + 2) (q ^ (k : ℕ)) := by
  match n with
  | 0 | 1 | 2 => omega
  | n + 3 => exact a.eq_4 n

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧ coeff 2 generatingSeries = 1 ∧
    X ^ 2 * (generatingSeries + 1) = generatingSeries.subst (X ^ 2 + X ^ 3) := by
  refine ⟨by simp [generatingSeries, a], by simp [generatingSeries, a],
    by simp [generatingSeries, a], ?_⟩
  change X ^ 2 * (generatingSeries + 1) = generatingSeries.subst q
  ext d
  by_cases hd : 2 ≤ d
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hd
    rw [Nat.add_comm 2 n]
    rw [coeff_X_pow_mul]
    by_cases hn : 3 ≤ n
    · rw [coeff_subst_cut _ _ n (by omega)]
      simpa [generatingSeries, coeff_one, show n ≠ 0 by omega] using a_step n hn
    · rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl <;>
        rw [coeff_subst_cut _ _ 3 (by omega)] <;>
        simp [Fin.sum_univ_succ, generatingSeries, a, coeff_q_pow, coeff_one]
  · rw [coeff_X_pow_mul', if_neg (by omega), coeff_subst_cut _ _ 1 (by omega)]
    simp [generatingSeries, a]

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 0)
    (h1 : coeff 1 B = 1) (h2 : coeff 2 B = 1)
    (hB : X ^ 2 * (B + 1) = B.subst (X ^ 2 + X ^ 3)) : B = generatingSeries := by
  have hc : ∀ n, coeff n B = a n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : 3 ≤ n
      · have he := congrArg (coeff (n + 2)) hB
        change coeff (n + 2) (X ^ 2 * (B + 1)) = coeff (n + 2) (B.subst q) at he
        rw [coeff_X_pow_mul, coeff_subst_cut _ _ n (by omega)] at he
        simp only [map_add, coeff_one, if_neg (by omega : n ≠ 0), add_zero] at he
        rw [he, a_step n hn]
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k k.isLt]
      · rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl <;>
          simp_all [a, coeff_zero_eq_constantCoeff]
  ext n
  simpa [generatingSeries] using hc n

theorem coeff_recurrence (n : ℕ) (hn : 3 ≤ n) :
    a n = ∑ k ∈ Finset.range (n / 2 + 2), a k * (k.choose (n + 2 - 2 * k) : ℤ) := by
  have he := congrArg (coeff (n + 2)) generating_equation.2.2.2
  change coeff (n + 2) (X ^ 2 * (generatingSeries + 1)) =
    coeff (n + 2) (generatingSeries.subst q) at he
  rw [coeff_X_pow_mul, coeff_subst_cut _ _ (n / 2 + 2) (by omega)] at he
  simp only [map_add, coeff_one, if_neg (by omega : n ≠ 0), add_zero,
    generatingSeries, coeff_mk] at he
  rw [he, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_q_pow, if_pos (by have := k.isLt; omega)]

private theorem choose_even_of_even_odd (k j : ℕ) (hk : k % 2 = 0) (hj : j % 2 = 1) :
    2 ∣ (k.choose j : ℤ) := by
  cases k with
  | zero => simp [Nat.choose_eq_zero_of_lt (by omega : 0 < j)]
  | succ k =>
    cases j with
    | zero => omega
    | succ j =>
      have he := congrArg (fun t : ℕ => t % 2) (Nat.add_one_mul_choose_eq k j)
      simp only [Nat.mul_mod, hk, hj, zero_mul, Nat.zero_mod, mul_one,
        Nat.mod_mod] at he
      exact_mod_cast (Nat.dvd_of_mod_eq_zero he.symm)

private theorem odd_descent (m : ℕ) (hm : 3 ≤ m) (hodd : m % 2 = 1) : 2 ∣ a m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [coeff_recurrence m hm]
    apply Finset.dvd_sum
    intro k hk
    have hbound := Finset.mem_range.mp hk
    have hsmall : k < m := by omega
    have hj : (m + 2 - 2 * k) % 2 = 1 := by omega
    by_cases hke : k % 2 = 0
    · exact dvd_mul_of_dvd_right (choose_even_of_even_odd k _ hke hj) _
    · by_cases hk3 : 3 ≤ k
      · exact dvd_mul_of_dvd_left (ih k hsmall hk3 (by omega)) _
      · have hk1 : k = 1 := by omega
        subst k
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
        exact dvd_zero 2

theorem hanna_conjecture (n : ℕ) (hn : 1 < n) : 2 ∣ a (2 * n - 1) := by
  exact odd_descent _ (by omega) (by omega)

#print axioms generating_equation
#print axioms generating_unique
#print axioms coeff_recurrence
#print axioms hanna_conjecture

end D5.S1.Recurrence.Parity.SquareCubeSubstitutionOddIndexParity

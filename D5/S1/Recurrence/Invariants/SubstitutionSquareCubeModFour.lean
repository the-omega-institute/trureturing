/- GID: D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The normalized square-cube series satisfies Hanna's mod-four conjecture. -/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.BigOperators.ModEq

open PowerSeries
open scoped BigOperators

namespace D5.S1.Recurrence.Invariants.SubstitutionSquareCubeModFour

private noncomputable def q : PowerSeries ℤ := X ^ 2 + 2 * X ^ 3

private theorem q_factor : q = X ^ 2 * (1 + C 2 * X) := by
  simp only [q, map_ofNat]
  ring

private theorem q_zero : constantCoeff q = 0 := by simp [q]

private theorem coeff_q_pow_zero (d k : ℕ) (h : d < 2 * k) :
    coeff d (q ^ k) = 0 := by
  rw [q_factor, mul_pow, ← pow_mul, coeff_X_pow_mul', if_neg (by omega)]

private theorem coeff_subst_cut (B : PowerSeries ℤ) (d N : ℕ) (h : d < 2 * N) :
    coeff d (B.subst q) = ∑ k : Fin N, coeff k B * coeff d (q ^ (k : ℕ)) := by
  rw [coeff_subst' (.of_constantCoeff_zero q_zero)]
  simp only [smul_eq_mul]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N)]
  · exact (Fin.sum_univ_eq_sum_range _ N).symm
  · intro k hk
    by_contra hnot
    have hNk : N ≤ k := by simpa using hnot
    have hz := coeff_q_pow_zero d k (by omega)
    exact hk (by simp [hz])

noncomputable def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => ∑ k : Fin (n + 2), a k * coeff (n + 3) (q ^ (k : ℕ))
termination_by n => n
decreasing_by exact k.isLt

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem a_step (n : ℕ) (hn : 2 ≤ n) :
    a n = ∑ k : Fin n, a k * coeff (n + 1) (q ^ (k : ℕ)) := by
  match n with
  | 0 | 1 => omega
  | n + 2 => exact a.eq_3 n

theorem generating_equation : constantCoeff generatingSeries = 0 ∧
    coeff 1 generatingSeries = 1 ∧
    X * generatingSeries = generatingSeries.subst (X ^ 2 + 2 * X ^ 3) := by
  refine ⟨by simp [generatingSeries, a], by simp [generatingSeries, a], ?_⟩
  change X * generatingSeries = generatingSeries.subst q
  ext d
  cases d with
  | zero =>
    rw [coeff_zero_eq_constantCoeff]
    simp only [map_mul, constantCoeff_X, zero_mul]
    exact (constantCoeff_subst_eq_zero q_zero _ (by simp [generatingSeries, a])).symm
  | succ n =>
    rw [coeff_succ_X_mul]
    by_cases hn : 2 ≤ n
    · rw [coeff_subst_cut _ (n + 1) n (by omega)]
      simpa [generatingSeries] using a_step n hn
    · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
      · rw [coeff_subst_cut _ 1 1 (by omega)]
        simp [generatingSeries, a]
      · rw [coeff_subst_cut _ 2 2 (by omega)]
        simp [Fin.sum_univ_two, generatingSeries, a, q, coeff_X_pow]
        rw [show (2 : PowerSeries ℤ) = C 2 from (map_ofNat C 2).symm,
          coeff_C_mul]
        simp

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 0)
    (h1 : coeff 1 B = 1)
    (hB : X * B = B.subst (X ^ 2 + 2 * X ^ 3)) : B = generatingSeries := by
  have hc : ∀ n, coeff n B = a n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : 2 ≤ n
      · have he := congrArg (coeff (n + 1)) hB
        change coeff (n + 1) (X * B) = coeff (n + 1) (B.subst q) at he
        rw [coeff_succ_X_mul, coeff_subst_cut _ _ n (by omega)] at he
        rw [he, a_step n hn]
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k k.isLt]
      · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;>
          simp_all [a, coeff_zero_eq_constantCoeff]
  ext n
  simpa [generatingSeries] using hc n

private theorem coeff_linear_pow (k j : ℕ) :
    coeff j ((1 + C 2 * X : PowerSeries ℤ) ^ k) = 2 ^ j * (k.choose j : ℤ) := by
  have hp : coeff j ((1 + X : PowerSeries ℤ) ^ k) = (k.choose j : ℤ) := by
    have h := Polynomial.coeff_one_add_X_pow ℤ k j
    rw [← Polynomial.coeff_coe] at h
    simpa using h
  have he := congrArg (coeff j) (map_pow (rescale (2 : ℤ)) (1 + X) k)
  rw [coeff_rescale, hp] at he
  simpa only [map_add, map_one, rescale_X] using he.symm

private theorem coeff_q_pow (d k : ℕ) :
    coeff d (q ^ k) = if 2 * k ≤ d then
      2 ^ (d - 2 * k) * (k.choose (d - 2 * k) : ℤ) else 0 := by
  rw [q_factor, mul_pow, ← pow_mul, coeff_X_pow_mul']
  simp only [coeff_linear_pow]

theorem coeff_recurrence (n : ℕ) (hn : 2 ≤ n) :
    a n = ∑ k : Fin n, if 2 * (k : ℕ) ≤ n + 1 then
      a k * 2 ^ (n + 1 - 2 * (k : ℕ)) *
        ((k : ℕ).choose (n + 1 - 2 * (k : ℕ)) : ℤ) else 0 := by
  have he := congrArg (coeff (n + 1)) generating_equation.2.2
  rw [coeff_succ_X_mul] at he
  rw [show coeff n generatingSeries = a n by simp [generatingSeries]] at he
  change a n = coeff (n + 1) (generatingSeries.subst q) at he
  rw [he, coeff_subst_cut _ _ n (by omega)]
  simp only [generatingSeries, coeff_mk]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_q_pow]
  split_ifs <;> simp [mul_assoc]

private theorem recurrence_kernel (n : ℕ) (hn : 2 ≤ n) :
    a n = ∑ k : Fin n, a k * coeff (n + 1) (q ^ (k : ℕ)) := by
  rw [coeff_recurrence n hn]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_q_pow]
  split_ifs <;> simp [mul_assoc]

private theorem coeff_q_tail_dvd (d k : ℕ) (h0 : d ≠ 2 * k)
    (h1 : d ≠ 2 * k + 1) : 4 ∣ coeff d (q ^ k) := by
  rw [coeff_q_pow]
  split_ifs with h
  · have hp : (2 : ℤ) ^ 2 ∣ 2 ^ (d - 2 * k) :=
      pow_dvd_pow 2 (by omega)
    exact dvd_mul_of_dvd_left hp _
  · exact dvd_zero 4

private theorem odd_contraction (m : ℕ) (hm : 2 ≤ m) :
    a (2 * m - 1) ≡ a m [ZMOD 4] := by
  rw [recurrence_kernel _ (by omega)]
  let i : Fin (2 * m - 1) := ⟨m, by omega⟩
  have hs : (∑ k : Fin (2 * m - 1), a k * coeff (2 * m - 1 + 1) (q ^ (k : ℕ))) ≡
      a i * coeff (2 * m - 1 + 1) (q ^ (i : ℕ)) [ZMOD 4] := by
    apply Int.sum_modEq_single (by simp)
    intro k hk hki
    apply Int.modEq_zero_iff_dvd.mpr
    apply dvd_mul_of_dvd_right
    apply coeff_q_tail_dvd
    · have hne : (k : ℕ) ≠ m := fun he => hki (Fin.ext he)
      omega
    · omega
  simpa [i, coeff_q_pow, show 2 * m - 1 + 1 = 2 * m by omega] using hs

private theorem even_contraction (m : ℕ) (hm : 1 ≤ m) :
    a (2 * m) ≡ 2 * (m : ℤ) * a m [ZMOD 4] := by
  rw [recurrence_kernel _ (by omega)]
  let i : Fin (2 * m) := ⟨m, by omega⟩
  have hs : (∑ k : Fin (2 * m), a k * coeff (2 * m + 1) (q ^ (k : ℕ))) ≡
      a i * coeff (2 * m + 1) (q ^ (i : ℕ)) [ZMOD 4] := by
    apply Int.sum_modEq_single (by simp)
    intro k hk hki
    apply Int.modEq_zero_iff_dvd.mpr
    apply dvd_mul_of_dvd_right
    apply coeff_q_tail_dvd
    · omega
    · have hne : (k : ℕ) ≠ m := fun he => hki (Fin.ext he)
      omega
  simpa [i, coeff_q_pow, mul_comm, mul_left_comm, mul_assoc] using hs

theorem a_even (n : ℕ) (hn : 2 ≤ n) : 2 ∣ a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hpar : n % 2 = 0
    · have he : n = 2 * (n / 2) := by omega
      have hc := (even_contraction (n / 2) (by omega)).of_dvd (by norm_num : (2 : ℤ) ∣ 4)
      rw [← he] at hc
      exact hc.dvd_iff.mpr (dvd_mul_of_dvd_left (dvd_mul_right 2 _) _)
    · have he : n = 2 * ((n + 1) / 2) - 1 := by omega
      have hc := (odd_contraction ((n + 1) / 2) (by omega)).of_dvd
        (by norm_num : (2 : ℤ) ∣ 4)
      rw [← he] at hc
      exact hc.dvd_iff.mpr (ih _ (by omega) (by omega))

private theorem even_zero (m : ℕ) (hm : 2 ≤ m) : a (2 * m) % 4 = 0 := by
  have hc := even_contraction m (by omega)
  have hd : (4 : ℤ) ∣ 2 * (m : ℤ) * a m := by
    obtain ⟨t, ht⟩ := a_even m hm
    refine ⟨(m : ℤ) * t, ?_⟩
    rw [ht]
    ring
  exact Int.emod_eq_zero_of_dvd (hc.dvd_iff.mpr hd)

private theorem even_not_power (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∃ k : ℕ, 2 * m = 2 ^ k + 1 := by
  rintro ⟨k, hk⟩
  cases k with
  | zero => simp at hk; omega
  | succ k => rw [pow_succ] at hk; omega

private theorem odd_power (m : ℕ) (hm : 2 ≤ m) :
    (∃ k : ℕ, 2 * m - 1 = 2 ^ k + 1) ↔ ∃ k : ℕ, m = 2 ^ k + 1 := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp at hk; omega
    | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [pow_succ]; omega⟩

private theorem two_iff (n : ℕ) (hn : 1 < n) :
    a n % 4 = 2 ↔ ∃ k : ℕ, n = 2 ^ k + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases htwo : n = 2
    · subst n
      have hc := even_contraction 1 (by omega)
      have hv : a 2 % 4 = 2 := by simpa [Int.ModEq, a] using hc
      exact iff_of_true hv ⟨0, rfl⟩
    · by_cases hpar : n % 2 = 0
      · have he : n = 2 * (n / 2) := by omega
        rw [he, even_zero _ (by omega)]
        exact iff_of_false (by omega) (even_not_power _ (by omega))
      · have he : n = 2 * ((n + 1) / 2) - 1 := by omega
        have hm : 2 ≤ (n + 1) / 2 := by omega
        have hc := odd_contraction ((n + 1) / 2) hm
        change a (2 * ((n + 1) / 2) - 1) % 4 = a ((n + 1) / 2) % 4 at hc
        rw [← he] at hc
        rw [hc, ih _ (by omega) (by omega)]
        simpa only [← he] using (odd_power _ hm).symm

theorem hanna_conjecture (n : ℕ) (hn : 1 < n) :
    (a n % 4 = 2 ↔ ∃ k : ℕ, n = 2 ^ k + 1) ∧
    (a n % 4 = 0 ↔ ¬ ∃ k : ℕ, n = 2 ^ k + 1) := by
  have ht := two_iff n hn
  have he : a n % 2 = 0 := Int.emod_eq_zero_of_dvd (a_even n (by omega))
  refine ⟨ht, ?_⟩
  constructor
  · intro hz hp
    have := ht.mpr hp
    omega
  · intro hp
    have hne : a n % 4 ≠ 2 := fun h => hp (ht.mp h)
    omega

#print axioms generating_equation
#print axioms generating_unique
#print axioms coeff_recurrence
#print axioms a_even
#print axioms hanna_conjecture

end D5.S1.Recurrence.Invariants.SubstitutionSquareCubeModFour


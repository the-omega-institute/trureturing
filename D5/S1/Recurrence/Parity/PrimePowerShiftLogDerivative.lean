/- GID: D5/S1/Recurrence/Parity/PrimePowerShiftLogDerivative
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/PrimePowerShiftLogDerivative
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integral prime-power recursion and logarithmic differentiation prove Hanna A393867. -/

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Choose.Dvd

open PowerSeries

namespace D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative

noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

theorem lt_prime (n : ℕ) (hn : 1 ≤ n) : n < prime n := by
  have := Nat.add_two_le_nth_prime (n - 1)
  unfold prime
  omega

private theorem prime_is_prime (n : ℕ) : Nat.Prime (prime n) :=
  Nat.prime_nth_prime _

private theorem prime_coeff (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 1 ≤ j) (hjp : j < p) :
    (p : ℤ) ∣ coeff j (B ^ p) := by
  classical
  have hz : constantCoeff (B - 1) = 0 := by simp [h0]
  have htop : coeff j ((B - 1) ^ p) = 0 :=
    X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hz) p) j hjp
  rw [show B = (B - 1) + 1 by ring, add_pow, map_sum]
  apply Finset.dvd_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  by_cases hi0 : i = 0
  · subst i
    simp [show j ≠ 0 by omega]
  by_cases hip : i = p
  · subst i
    simp [htop]
  have hd : (p : ℤ) ∣ (p.choose i : ℤ) :=
    Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self hi0 (by omega))
  have hc : (↑(p.choose i) : PowerSeries ℤ) = C (p.choose i : ℤ) := by simp
  rw [one_pow, mul_one, hc, coeff_mul_C]
  exact dvd_mul_of_dvd_right hd _

private def Agree (n : ℕ) (B D : PowerSeries ℤ) : Prop :=
  ∀ j < n, coeff j B = coeff j D

private theorem agree_iff (n : ℕ) (B D : PowerSeries ℤ) :
    Agree n B D ↔ (X : PowerSeries ℤ) ^ n ∣ B - D := by
  simp [Agree, X_pow_dvd_iff, map_sub, sub_eq_zero]

private theorem agree_pow {n : ℕ} {B D : PowerSeries ℤ}
    (h : Agree n B D) (p : ℕ) : Agree n (B ^ p) (D ^ p) :=
  (agree_iff _ _ _).mpr
    (((agree_iff _ _ _).mp h).trans (sub_dvd_pow_sub_pow B D p))

private theorem coeff_mul_vanish {n : ℕ} {B : PowerSeries ℤ}
    (h : ∀ j < n, coeff j B = 0) (D : PowerSeries ℤ) :
    coeff n (B * D) = coeff n B * constantCoeff D := by
  obtain ⟨T, rfl⟩ := X_pow_dvd_iff.mpr h
  rw [mul_assoc]
  have hm (S : PowerSeries ℤ) : coeff n (X ^ n * S) = constantCoeff S := by
    simpa only [zero_add, coeff_zero_eq_constantCoeff] using coeff_X_pow_mul S n 0
  rw [hm, hm, map_mul]

private theorem pow_coeff_change {n : ℕ} {B D : PowerSeries ℤ}
    (hB : constantCoeff B = 1) (hD : constantCoeff D = 1)
    (h : Agree n B D) (p : ℕ) :
    coeff n (B ^ p) - coeff n (D ^ p) =
      (p : ℤ) * (coeff n B - coeff n D) := by
  classical
  rw [← map_sub, ← geom_sum₂_mul]
  rw [mul_comm, coeff_mul_vanish]
  · simp [map_sum, hB, hD, map_sub, mul_comm]
  · intro j hj
    simp [map_sub, h j hj]

private noncomputable def correction (n : ℕ) (B : PowerSeries ℤ) : ℤ :=
  ((prime n : ℤ) * coeff (n - 1) (B ^ prime n) - coeff n (B ^ prime n)) / prime n

private noncomputable def advance (n : ℕ) (B : PowerSeries ℤ) : PowerSeries ℤ :=
  B + C (correction n B) * X ^ n

private theorem advance_agree (n : ℕ) (B : PowerSeries ℤ) : Agree n (advance n B) B := by
  intro j hj
  simp only [advance, map_add, coeff_C_mul_X_pow, if_neg (by omega : j ≠ n), add_zero]

private theorem advance_zero {n : ℕ} (hn : 1 ≤ n) (B : PowerSeries ℤ)
    (h0 : constantCoeff B = 1) : constantCoeff (advance n B) = 1 := by
  simp [advance, h0, show n ≠ 0 by omega]

private theorem advance_equation {n : ℕ} (hn : 1 ≤ n) (B : PowerSeries ℤ)
    (h0 : constantCoeff B = 1) :
    coeff n ((advance n B) ^ prime n) =
      (prime n : ℤ) * coeff (n - 1) ((advance n B) ^ prime n) := by
  have hd : (prime n : ℤ) ∣
      (prime n : ℤ) * coeff (n - 1) (B ^ prime n) - coeff n (B ^ prime n) :=
    dvd_sub (dvd_mul_right _ _) (prime_coeff B h0 (prime_is_prime n) hn (lt_prime n hn))
  have hc := Int.mul_ediv_cancel' hd
  have he := pow_coeff_change (advance_zero hn B h0) h0 (advance_agree n B) (prime n)
  have hl := agree_pow (advance_agree n B) (prime n) (n - 1) (by omega)
  have hadd : coeff n (advance n B) - coeff n B = correction n B := by
    simp only [advance, map_add, coeff_C_mul_X_pow, ↓reduceIte, add_sub_cancel_left]
  rw [hadd] at he
  rw [hl]
  change (prime n : ℤ) * correction n B = _ at hc
  linear_combination he + hc

private noncomputable def approximation : ℕ → PowerSeries ℤ
  | 0 => 1
  | n + 1 => advance (n + 1) (approximation n)

private theorem approximation_zero (n : ℕ) : constantCoeff (approximation n) = 1 := by
  induction n with
  | zero => simp [approximation]
  | succ n ih => exact advance_zero (by omega) _ ih

private theorem approximation_stable {s t : ℕ} (h : s ≤ t) :
    Agree (s + 1) (approximation s) (approximation t) := by
  induction t, h using Nat.le_induction with
  | base => intro j hj; rfl
  | succ t hst ih =>
    intro j hj
    exact (ih j hj).trans ((advance_agree (t + 1) (approximation t)) j (by omega)).symm

noncomputable def a (n : ℕ) : ℤ := coeff n (approximation n)

noncomputable def generatingSeries : PowerSeries ℤ := mk a

private theorem generating_agree (s : ℕ) : Agree (s + 1) generatingSeries (approximation s) := by
  intro j hj
  simpa only [generatingSeries, coeff_mk, a] using
    approximation_stable (s := j) (t := s) (by omega) j (by omega)

theorem generating_equation : constantCoeff generatingSeries = 1 ∧
    ∀ n, 1 ≤ n → coeff n (generatingSeries ^ prime n) =
      (prime n : ℤ) * coeff (n - 1) (generatingSeries ^ prime n) := by
  constructor
  · simpa only [coeff_zero_eq_constantCoeff, approximation, map_one] using
      generating_agree 0 0 (by omega)
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [agree_pow (generating_agree (k + 1)) _ (k + 1) (by omega),
      agree_pow (generating_agree (k + 1)) _ (k + 1 - 1) (by omega)]
    exact advance_equation hn _ (approximation_zero k)

theorem generating_unique (B : PowerSeries ℤ) (h0 : constantCoeff B = 1)
    (hB : ∀ n, 1 ≤ n → coeff n (B ^ prime n) =
      (prime n : ℤ) * coeff (n - 1) (B ^ prime n)) : B = generatingSeries := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simpa only [coeff_zero_eq_constantCoeff, generating_equation.1] using h0
    have hag : Agree n B generatingSeries := ih
    have hp : (prime n : ℤ) ≠ 0 := by exact_mod_cast (prime_is_prime n).ne_zero
    have he := pow_coeff_change h0 generating_equation.1 hag (prime n)
    rw [hB n (by omega), generating_equation.2 n (by omega),
      agree_pow hag _ (n - 1) (by omega), sub_self] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left hp)

theorem prime_dvd_coeff_pow (n j : ℕ) (hj : 1 ≤ j) (hjp : j < prime n) :
    (prime n : ℤ) ∣ coeff j (generatingSeries ^ prime n) :=
  prime_coeff _ generating_equation.1 (prime_is_prime n) hj hjp

noncomputable def logDerivative : PowerSeries ℤ :=
  derivative ℤ generatingSeries * invOfUnit generatingSeries 1

noncomputable def a393867 (n : ℕ) : ℤ := coeff (n - 1) logDerivative

private theorem log_mul : logDerivative * generatingSeries = derivative ℤ generatingSeries := by
  rw [logDerivative, mul_assoc, invOfUnit_mul _ 1 generating_equation.1, mul_one]

private theorem derivative_identity (n : ℕ) :
    derivative ℤ (generatingSeries ^ n) = C (n : ℤ) * logDerivative * generatingSeries ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_pow, Nat.add_sub_cancel, pow_succ, ← log_mul]
    have hc : (↑(n + 1) : PowerSeries ℤ) = C ((n + 1 : ℕ) : ℤ) := by simp
    rw [hc]
    ring

theorem log_derivative_identity (n : ℕ) :
    X * derivative ℤ (generatingSeries ^ n) =
      C (n : ℤ) * (X * logDerivative) * generatingSeries ^ n := by
  rw [derivative_identity]
  ring

private theorem coeff_mul_dvd_sub (L H : PowerSeries ℤ) (h0 : constantCoeff H = 1)
    (p : ℤ) (m : ℕ) (hH : ∀ j, 1 ≤ j → j ≤ m → p ∣ coeff j H) :
    p ∣ coeff m (L * H) - coeff m L := by
  classical
  have hm : (m, 0) ∈ Finset.antidiagonal m := by simp
  rw [coeff_mul, ← Finset.sum_erase_add _ _ hm]
  simp only [coeff_zero_eq_constantCoeff, h0, mul_one, add_sub_cancel_right]
  apply Finset.dvd_sum
  rintro ⟨i, j⟩ hij
  have hne := (Finset.mem_erase.mp hij).1
  have hsum := Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hij).2
  have hj : 1 ≤ j := by
    by_contra h
    apply hne
    apply Prod.ext <;> simp only <;> omega
  exact dvd_mul_of_dvd_right (hH j hj (by omega)) _

theorem hanna_conjecture (n : ℕ) (hn : 1 < n) : (prime n : ℤ) ∣ a393867 n := by
  have hn1 : 1 ≤ n := by omega
  have hp : (prime n : ℤ) ≠ 0 := by exact_mod_cast (prime_is_prime n).ne_zero
  have he := congrArg (coeff (n - 1)) (derivative_identity (prime n))
  rw [coeff_derivative, Nat.sub_add_cancel hn1, mul_assoc, coeff_C_mul] at he
  rw [show ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) by omega] at he
  rw [generating_equation.2 n hn1] at he
  have he' : (n : ℤ) * coeff (n - 1) (generatingSeries ^ prime n) =
      coeff (n - 1) (logDerivative * generatingSeries ^ prime n) := by
    apply mul_left_cancel₀ hp
    linear_combination he
  have hd : (prime n : ℤ) ∣ coeff (n - 1) (logDerivative * generatingSeries ^ prime n) := by
    rw [← he']
    exact dvd_mul_of_dvd_right
      (prime_dvd_coeff_pow n (n - 1) (by omega) (by have := lt_prime n hn1; omega)) _
  have hr := coeff_mul_dvd_sub logDerivative (generatingSeries ^ prime n)
    (by simp [generating_equation.1]) (prime n) (n - 1) (by
      intro j hj hjn
      exact prime_dvd_coeff_pow n j hj (by have := lt_prime n hn1; omega))
  have := dvd_sub hd hr
  simpa only [sub_sub_cancel, a393867] using this

theorem printed_formula_false :
    ¬ ∀ n, 1 < n → (prime n : ℤ) ∣ coeff n logDerivative := by
  have h1 : coeff 1 generatingSeries = 1 := by
    have h := generating_equation.2 1 (by omega)
    norm_num [prime, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ,
      generating_equation.1] at h
    omega
  have h2 : coeff 2 generatingSeries = 2 := by
    have h := generating_equation.2 2 (by omega)
    norm_num [prime, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ,
      generating_equation.1, h1] at h
    omega
  have h3 : coeff 3 generatingSeries = 10 := by
    have h := generating_equation.2 3 (by omega)
    norm_num [prime, pow_succ, coeff_mul, Finset.Nat.antidiagonal_succ,
      generating_equation.1, h1, h2] at h
    omega
  have hl0 : constantCoeff logDerivative = 1 := by
    have h := congrArg (coeff 0) log_mul
    simpa [coeff_derivative, generating_equation.1, h1] using h
  have hl1 : coeff 1 logDerivative = 3 := by
    have h := congrArg (coeff 1) log_mul
    norm_num [coeff_mul, coeff_derivative, Finset.Nat.antidiagonal_succ,
      generating_equation.1, h1, h2, hl0] at h
    omega
  have hl2 : coeff 2 logDerivative = 25 := by
    have h := congrArg (coeff 2) log_mul
    norm_num [coeff_mul, coeff_derivative, Finset.Nat.antidiagonal_succ,
      generating_equation.1, h1, h2, h3, hl0, hl1] at h
    omega
  intro h
  have := h 2 (by omega)
  norm_num [prime, hl2] at this

#print axioms lt_prime
#print axioms generating_equation
#print axioms generating_unique
#print axioms prime_dvd_coeff_pow
#print axioms log_derivative_identity
#print axioms hanna_conjecture
#print axioms printed_formula_false

end D5.S1.Recurrence.Parity.PrimePowerShiftLogDerivative

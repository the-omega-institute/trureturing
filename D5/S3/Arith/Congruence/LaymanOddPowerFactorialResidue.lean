/- GID: D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/LaymanOddPowerFactorialResidue
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Wilson]
   utility: none
   digest: Odd powers of n! have Layman's classified residue modulo n(n+1)/2. -/

import Mathlib.NumberTheory.Wilson

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.Congruence.LaymanOddPowerFactorialResidue

/-- Outside the odd-prime branch, the triangular modulus divides the factorial. -/
theorem factorial_dvd_triangular_of_not_odd_prime
    {n : ℕ} (hn : 1 ≤ n)
    (h : ¬(Nat.Prime (n + 1) ∧ Odd (n + 1))) :
    n * (n + 1) / 2 ∣ n.factorial := by
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · have hn1_odd : Odd (n + 1) := hn_even.add_one
    have hn1_not_prime : ¬Nat.Prime (n + 1) := fun hp => h ⟨hp, hn1_odd⟩
    have hn1_two : 2 ≤ n + 1 := by omega
    rcases (Nat.not_prime_iff_exists_mul_eq hn1_two).mp hn1_not_prime with
      ⟨a, b, ha_lt, hb_lt, hab⟩
    have ha_two : 2 ≤ a := by
      have ha0 : a ≠ 0 := by
        intro ha
        subst a
        simp at hab
      have ha1 : a ≠ 1 := by
        intro ha
        subst a
        simp at hab
        omega
      omega
    have hb_two : 2 ≤ b := by
      have hb0 : b ≠ 0 := by
        intro hb
        subst b
        simp at hab
      have hb1 : b ≠ 1 := by
        intro hb
        subst b
        simp at hab
        omega
      omega
    have hab_odd : Odd (a * b) := by simpa [hab] using hn1_odd
    have hab_sum_lt : a + b < a * b := by
      apply Nat.lt_of_le_of_ne (Nat.add_le_mul ha_two hb_two)
      intro heq
      have hsum_even : Even (a + b) :=
        (Nat.Odd.of_mul_left hab_odd).add_odd (Nat.Odd.of_mul_right hab_odd)
      have hsum_odd : Odd (a + b) := heq ▸ hab_odd
      exact (Nat.not_even_iff_odd.mpr hsum_odd) hsum_even
    have hab_sum_le_n : a + b ≤ n := by omega
    have ha_dvd : a ∣ a.factorial := Nat.dvd_factorial (by omega) le_rfl
    have hb_dvd : b ∣ b.factorial := Nat.dvd_factorial (by omega) le_rfl
    have hn1_dvd : n + 1 ∣ n.factorial := by
      rw [← hab]
      exact (Nat.mul_dvd_mul ha_dvd hb_dvd).trans
        ((Nat.factorial_mul_factorial_dvd_factorial_add a b).trans
          (Nat.factorial_dvd_factorial hab_sum_le_n))
    have hn_half_pos : 0 < n / 2 :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hn_even.two_dvd) (by decide)
    have hn_half_dvd : n / 2 ∣ n.factorial :=
      Nat.dvd_factorial hn_half_pos (Nat.div_le_self n 2)
    have hn_coprime : n.Coprime (n + 1) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.coprime_one_right n
    have hcop : (n / 2).Coprime (n + 1) :=
      Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hn_even.two_dvd) hn_coprime
    rw [mul_comm n, Nat.mul_div_assoc (n + 1) hn_even.two_dvd, mul_comm]
    exact hcop.mul_dvd_of_dvd_of_dvd hn_half_dvd hn1_dvd
  · have hn1_even : Even (n + 1) := hn_odd.add_one
    have hn_dvd : n ∣ n.factorial := Nat.dvd_factorial (by omega) le_rfl
    have hn1_half_pos : 0 < (n + 1) / 2 := Nat.div_pos (by omega) (by decide)
    have hn1_half_dvd : (n + 1) / 2 ∣ n.factorial :=
      Nat.dvd_factorial hn1_half_pos (by omega)
    have hn_coprime : n.Coprime (n + 1) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.coprime_one_right n
    have hcop : n.Coprime ((n + 1) / 2) :=
      Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd hn1_even.two_dvd) hn_coprime
    rw [Nat.mul_div_assoc n hn1_even.two_dvd]
    exact hcop.mul_dvd_of_dvd_of_dvd hn_dvd hn1_half_dvd

/-- Layman's odd-power generalization of the A119690 residue formula. -/
theorem result : ∀ n k : ℕ, 1 ≤ n →
    n.factorial ^ (2 * k + 1) % (n * (n + 1) / 2) =
      if Nat.Prime (n + 1) ∧ Odd (n + 1) then n else 0 := by
  intro n k hn
  split_ifs with hbranch
  · rcases hbranch with ⟨hp, hn1_odd⟩
    have hn_even : Even n :=
      Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hn1_odd)
    have hn_two : 2 ≤ n := Nat.le_of_dvd (by omega) hn_even.two_dvd
    have hn_half_pos : 0 < n / 2 := Nat.div_pos hn_two (by decide)
    have hn_half_dvd_n : n / 2 ∣ n := Nat.div_dvd_of_dvd hn_even.two_dvd
    have hn_half_dvd_fac : n / 2 ∣ n.factorial :=
      Nat.dvd_factorial hn_half_pos (Nat.div_le_self n 2)
    have hpow_half_dvd : n / 2 ∣ n.factorial ^ (2 * k + 1) :=
      dvd_pow hn_half_dvd_fac (by omega)
    have hmod_half : n.factorial ^ (2 * k + 1) ≡ n [MOD n / 2] :=
      (Nat.modEq_zero_iff_dvd.mpr hpow_half_dvd).trans
        (Nat.modEq_zero_iff_dvd.mpr hn_half_dvd_n).symm
    have hmod_prime : n.factorial ^ (2 * k + 1) ≡ n [MOD n + 1] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      let _ : Fact (Nat.Prime (n + 1)) := ⟨hp⟩
      have hw : ((n.factorial : ℕ) : ZMod (n + 1)) = -1 := by
        simpa using ZMod.wilsons_lemma (n + 1)
      have hn_cast : ((n : ZMod (n + 1))) = -1 := by
        apply eq_neg_of_add_eq_zero_left
        simpa only [Nat.cast_add, Nat.cast_one] using ZMod.natCast_self (n + 1)
      calc
        ((n.factorial ^ (2 * k + 1) : ℕ) : ZMod (n + 1)) =
            ((n.factorial : ℕ) : ZMod (n + 1)) ^ (2 * k + 1) := by simp
        _ = (-1 : ZMod (n + 1)) ^ (2 * k + 1) := by rw [hw]
        _ = -1 := by simp [pow_add, pow_mul]
        _ = n := hn_cast.symm
    have hn_coprime : n.Coprime (n + 1) := by
      rw [Nat.coprime_self_add_right]
      exact Nat.coprime_one_right n
    have hcop : (n / 2).Coprime (n + 1) :=
      Nat.Coprime.of_dvd_left hn_half_dvd_n hn_coprime
    have hcrt : n.factorial ^ (2 * k + 1) ≡ n [MOD (n / 2) * (n + 1)] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmod_half, hmod_prime⟩
    have hn_lt : n < (n / 2) * (n + 1) := by
      calc
        n < n + 1 := by omega
        _ = 1 * (n + 1) := by simp
        _ ≤ (n / 2) * (n + 1) := Nat.mul_le_mul_right (n + 1) hn_half_pos
    rw [mul_comm n (n + 1), Nat.mul_div_assoc (n + 1) hn_even.two_dvd,
      mul_comm (n + 1) (n / 2)]
    calc
      n.factorial ^ (2 * k + 1) % ((n / 2) * (n + 1)) =
          n % ((n / 2) * (n + 1)) := hcrt
      _ = n := Nat.mod_eq_of_lt hn_lt
  · exact Nat.mod_eq_zero_of_dvd
      (dvd_pow (factorial_dvd_triangular_of_not_odd_prime hn hbranch) (by omega))

#print axioms factorial_dvd_triangular_of_not_odd_prime
#print axioms result

end D5.S3.Arith.Congruence.LaymanOddPowerFactorialResidue

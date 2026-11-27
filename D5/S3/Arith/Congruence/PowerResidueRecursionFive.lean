/- GID: D5/S3/Arith/Congruence/PowerResidueRecursionFive
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/PowerResidueRecursionFive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every index at which the original A374911 recursion takes value five is even. -/

import D5.S3.Arith.Congruence.PowerResidueRecursionFour
import OmegaBuild.Commands

/-! # Parity of the indices at value five in OEIS A374911 -/

compile_only_with_mathlib

namespace D5.S3.Arith.Congruence.PowerResidueRecursionFive

open PowerResidueRecursionFour

private theorem leastPrimeFactor_modEq_one_of_pow_self {a n : ℕ} (hn : 1 < n)
    (h : Nat.ModEq n (a ^ n) 1) : Nat.ModEq n.minFac a 1 := by
  let p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  let : Fact p.Prime := ⟨hp⟩
  have hpow : (a : ZMod p) ^ n = 1 := by
    have hmod := h.of_dvd (Nat.minFac_dvd n)
    simpa only [Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (a ^ n) 1 p).mpr hmod
  have hne : (a : ZMod p) ≠ 0 := by
    intro hzero
    simp [hzero, zero_pow (by omega : n ≠ 0)] at hpow
  have hp₂ := hp.two_le
  have hc : n.Coprime (p - 1) :=
    Nat.coprime_of_lt_minFac (by omega) (by change p - 1 < p; omega)
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow)
    (ZMod.orderOf_dvd_card_sub_one hne)
  rw [hc.gcd_eq_one] at hd
  have ha : (a : ZMod p) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  exact (ZMod.natCast_eq_natCast_iff a 1 p).mp (by simpa using ha)

private theorem valueFive_characterization (n : ℕ) : seq n = 5 ↔
    3 ^ n % n = 1 ∧ ∃ k : ℕ, 0 < k ∧ 2 ^ n % n = 2 ^ k := by
  have at_zero := (seq_eq_one 0).mpr rfl
  have at_one := (seq_eq_two 1).mpr rfl
  have lower_bound (m : ℕ) : min 3 (m + 1) ≤ seq m := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases hm : m = 0
      · subst m
        simp [at_zero]
      by_cases hm₁ : m = 1
      · subst m
        simp [at_one]
      have hm_pos := Nat.pos_of_ne_zero hm
      have left := ih _ (Nat.mod_lt (2 ^ m) hm_pos)
      have right := ih _ (Nat.mod_lt (3 ^ m) hm_pos)
      have hrec : seq m = seq (2 ^ m % m) + seq (3 ^ m % m) := by
        conv_lhs => rw [seq.eq_def, dite_eq_right hm]
      have hne : seq m ≠ 2 := fun h => hm₁ ((seq_eq_two m).mp h)
      omega
  constructor
  · intro hs
    have hn : 1 < n := by
      by_contra! h
      have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl <;> omega
    have hrec : seq n = seq (2 ^ n % n) + seq (3 ^ n % n) := by
      conv_lhs => rw [seq.eq_def, dite_eq_right (by omega : n ≠ 0)]
    have left := lower_bound (2 ^ n % n)
    have right := lower_bound (3 ^ n % n)
    have left_ne_one : seq (2 ^ n % n) ≠ 1 := by
      intro h
      obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        (Nat.dvd_of_mod_eq_zero ((seq_eq_one _).mp h))
      have hk_pos : 0 < k := by
        by_contra! hk_zero
        have : k = 0 := by omega
        simp [this] at hk
        omega
      have := (seq_eq_three n).mpr ⟨k, hk_pos, hk⟩
      omega
    have left_ne_two : seq (2 ^ n % n) ≠ 2 := by
      intro h
      have hpow : Nat.ModEq n (2 ^ n) 1 := by
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hn] using (seq_eq_two _).mp h
      have hp := Nat.minFac_prime (by omega : n ≠ 1)
      have hmod := leastPrimeFactor_modEq_one_of_pow_self hn hpow
      have hd : n.minFac ∣ 1 := (Nat.modEq_iff_dvd' (by decide : 1 ≤ 2)).mp hmod.symm
      exact hp.ne_one (Nat.dvd_one.mp hd)
    have right_ne_one : seq (3 ^ n % n) ≠ 1 := by
      intro h
      have hp := Nat.minFac_prime (by omega : n ≠ 1)
      have hd := Nat.dvd_of_mod_eq_zero ((seq_eq_one _).mp h)
      have hprime : n.minFac ∣ 3 := hp.dvd_of_dvd_pow ((Nat.minFac_dvd n).trans hd)
      have hfac := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hprime
      have hd₃ : 3 ∣ n := hfac ▸ Nat.minFac_dvd n
      have hfour : seq (2 ^ n % n) = 4 := by omega
      have hleft : 3 ∣ 2 ^ n % n := by
        rcases (a374911_eq_four _).mp hfour with h₃ | h₉
        · rw [h₃]
        · rw [h₉]
          decide
      have hpow : 3 ∣ 2 ^ n := by
        apply Nat.dvd_of_mod_eq_zero
        rw [← Nat.mod_mod_of_dvd (2 ^ n) hd₃, Nat.mod_eq_zero_of_dvd hleft]
      exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hpow)
    exact ⟨(seq_eq_two _).mp (by omega), (seq_eq_three _).mp (by omega)⟩
  · rintro ⟨h₃, k, hk, h₂⟩
    have hn : n ≠ 0 := by
      rintro rfl
      have hgt := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (Nat.ne_of_gt hk)
      simp at h₂
      omega
    have left := (seq_eq_three _).mpr ⟨k, hk, h₂⟩
    have right := (seq_eq_two _).mpr h₃
    conv_lhs => rw [seq.eq_def, dite_eq_right hn]
    omega

/-- Every index at which the original OEIS A374911 sequence takes value five is even. -/
theorem oeisA374911_valueFive_even (n : ℕ) (h : seq n = 5) : 2 ∣ n := by
  have h₃ := ((valueFive_characterization n).mp h).1
  by_cases h₀ : n = 0
  · simp [h₀]
  have h₁ : n ≠ 1 := by
    rintro rfl
    simp at h₃
  have hn : 1 < n := by omega
  have hpow : Nat.ModEq n (3 ^ n) 1 := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hn] using h₃
  have hmod := leastPrimeFactor_modEq_one_of_pow_self hn hpow
  have hd : n.minFac ∣ 2 := (Nat.modEq_iff_dvd' (by decide : 1 ≤ 3)).mp hmod.symm
  have hp := Nat.minFac_prime h₁
  have hfac := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
  exact hfac ▸ Nat.minFac_dvd n

#print axioms oeisA374911_valueFive_even

end D5.S3.Arith.Congruence.PowerResidueRecursionFive

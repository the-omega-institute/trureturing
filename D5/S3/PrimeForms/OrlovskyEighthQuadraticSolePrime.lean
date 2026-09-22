/- GID: D5/S3/PrimeForms/OrlovskyEighthQuadraticSolePrime
   generality: I
   mirror-B: D5/B/S3/PrimeForms/OrlovskyEighthQuadraticSolePrime
   mirror-E: none(waiver:unbounded-arithmetic-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Prime.Basic, mathlib/module/Mathlib.Tactic.IntervalCases, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Positive integral values of k(k+9)/8 have 17 as their sole prime. -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.OrlovskyEighthQuadraticSolePrime

/-- An integral value of the quadratic form with a positive natural parameter. -/
def IsTerm (a : ℕ) : Prop := ∃ k : ℕ, 0 < k ∧ 8 * a = k * (k + 9)

theorem result :
    (∀ k : ℕ, 0 < k → (8 ∣ k * (k + 9) ↔ ∃ m : ℕ, 0 < m ∧ (k + 1 = 8 * m ∨ k = 8 * m)))
      ∧ (IsTerm 17 ∧ Nat.Prime 17)
      ∧ (∀ a : ℕ, IsTerm a → a ≠ 17 → 1 < a ∧ ¬ Nat.Prime a) := by
  have classification : ∀ k : ℕ, 0 < k →
      (8 ∣ k * (k + 9) ↔ ∃ m : ℕ, 0 < m ∧ (k + 1 = 8 * m ∨ k = 8 * m)) := by
    intro k hk
    constructor
    · intro hd
      have hprod : k % 8 * ((k % 8 + 1) % 8) % 8 = 0 := by
        simpa [Nat.mul_mod, Nat.add_mod] using Nat.dvd_iff_mod_eq_zero.mp hd
      have hres : k % 8 = 0 ∨ k % 8 = 7 := by
        have hlt := Nat.mod_lt k (by decide : 0 < 8)
        interval_cases hr : k % 8 <;> norm_num [hr] at hprod <;> omega
      rcases hres with hr | hr
      · obtain ⟨m, hm⟩ := Nat.dvd_iff_mod_eq_zero.mpr hr
        exact ⟨m, by omega, Or.inr hm⟩
      · have hsucc : (k + 1) % 8 = 0 := by
          simp [Nat.add_mod, hr]
        obtain ⟨m, hm⟩ := Nat.dvd_iff_mod_eq_zero.mpr hsucc
        exact ⟨m, by omega, Or.inl hm⟩
    · rintro ⟨m, hmpos, hm | hm⟩
      · have hplus : k + 9 = 8 * (m + 1) := by omega
        exact dvd_mul_of_dvd_right ⟨m + 1, hplus⟩ k
      · exact dvd_mul_of_dvd_left ⟨m, hm⟩ (k + 9)
  refine ⟨classification, ?_, ?_⟩
  · constructor
    · exact ⟨8, by decide, by decide⟩
    · decide
  · rintro a ⟨k, hk, hka⟩ hne
    have hd : 8 ∣ k * (k + 9) := ⟨a, hka.symm⟩
    obtain ⟨m, hmpos, hm | hm⟩ := (classification k hk).mp hd
    · have hplus : k + 9 = 8 * (m + 1) := by omega
      have ha : a = k * (m + 1) := by
        apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 8)
        calc
          8 * a = k * (k + 9) := hka
          _ = 8 * (k * (m + 1)) := by rw [hplus]; ring
      have hklarge : 1 < k := by omega
      rw [ha]
      exact ⟨Nat.one_lt_mul_iff.mpr ⟨hk, by omega, Or.inl hklarge⟩,
        Nat.not_prime_mul (by omega) (by omega)⟩
    · have ha : a = m * (8 * m + 9) := by
        apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 8)
        calc
          8 * a = k * (k + 9) := hka
          _ = 8 * (m * (8 * m + 9)) := by rw [hm]; ring
      have hmne : m ≠ 1 := by
        intro h
        apply hne
        simpa [h] using ha
      rw [ha]
      exact ⟨Nat.one_lt_mul_iff.mpr ⟨hmpos, by omega, Or.inr (by omega)⟩,
        Nat.not_prime_mul hmne (by omega)⟩

end D5.S3.PrimeForms.OrlovskyEighthQuadraticSolePrime

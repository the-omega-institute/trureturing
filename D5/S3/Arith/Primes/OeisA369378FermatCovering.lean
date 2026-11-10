/- GID: D5/S3/Arith/Primes/OeisA369378FermatCovering
   generality: G
   mirror-B: D5/B/S3/Arith/Primes/OeisA369378FermatCovering
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Ordowski's A369378 Fermat covering settlement. -/

/-
claim: proof_shape: bind-only (convention-fixed definition); consumer: result.
result: proof_shape: bind-only; escape_witness: none; consumer: settling result.
admission_basis: open-problem-resolution (#18631; Proved).
Direct frozen dependencies: none; the proof uses only pinned Mathlib declarations.
The public claim is stated with the preregistered expression; the proof reuses Mathlib
odd-part and modular-arithmetic declarations without introducing a duplicate definition.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/26202.
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false

namespace D5.S3.Arith.Primes.OeisA369378FermatCovering

/-- The conjecture of A369378: "if n > 0, then 2^(2^n+1)-1 + 2^k is not prime for every k < 2^n". -/
def claim : Prop := ∀ n k : ℕ, 0 < n → k < 2 ^ n → ¬ (2 ^ (2 ^ n + 1) - 1 + 2 ^ k).Prime

/-! Fidelity checks (not part of the conventions): the published a(1) = 2 and a(2) = 4, that is,
`k = 2^n` gives a prime for n = 1, 2, so the bound `k < 2^n` is sharp there. -/

example : (2 ^ (2 ^ 1 + 1) - 1 + 2 ^ 2).Prime ∧ (2 ^ (2 ^ 2 + 1) - 1 + 2 ^ 4).Prime := by
  show Nat.Prime 11 ∧ Nat.Prime 47
  exact ⟨by norm_num, by norm_num⟩

theorem result : claim := by
  intro n k hn hk
  have hpow : 1 ≤ 2 ^ (2 ^ n + 1) := Nat.one_le_pow _ _ (by decide)
  by_cases hk0 : k = 0
  · subst k
    simp only [pow_zero, Nat.sub_add_cancel hpow]
    apply Nat.not_prime_of_dvd_of_lt (dvd_pow_self 2 (by omega : 2 ^ n + 1 ≠ 0)) (by omega)
    have he : 1 < 2 ^ n + 1 := Nat.AtLeastTwo.one_lt
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mpr he
    simpa using this
  · obtain ⟨j, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hk0
    have hmpos : 0 < m := hm.pos
    have hjn : j < n := by
      have hle : 2 ^ j ≤ k := by
        rw [hkm]
        exact Nat.le_mul_of_pos_right _ hmpos
      exact (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp (lt_of_le_of_lt hle hk)
    let F : ℕ := 2 ^ (2 ^ j) + 1
    have hbase : (2 : ZMod F) ^ (2 ^ j) = -1 := by
      have hz := ZMod.natCast_self F
      dsimp [F] at hz
      push_cast at hz
      exact eq_neg_of_add_eq_zero_left hz
    have hperiod : (2 : ZMod F) ^ (2 ^ (j + 1)) = 1 := by
      rw [pow_succ, pow_mul, hbase]
      norm_num
    have hlarge : (2 : ZMod F) ^ (2 ^ n) = 1 := by
      obtain ⟨q, hq⟩ := Nat.pow_dvd_pow 2 (by omega : j + 1 ≤ n)
      rw [hq, pow_mul, hperiod, one_pow]
    have hsmall : (2 : ZMod F) ^ k = -1 := by
      rw [hkm, pow_mul, hbase, hm.neg_one_pow]
    have hdvd : F ∣ 2 ^ (2 ^ n + 1) - 1 + 2 ^ k := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [Nat.cast_add, Nat.cast_sub hpow]
      push_cast
      rw [pow_succ, hlarge, hsmall]
      ring
    apply Nat.not_prime_of_dvd_of_lt hdvd
    · dsimp [F]
      have : 0 < 2 ^ (2 ^ j) := by positivity
      omega
    · have hjle : 2 ^ j < 2 ^ n + 1 := by
        have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mpr hjn
        omega
      have hlt : 2 ^ (2 ^ j) < 2 ^ (2 ^ n + 1) :=
        (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mpr hjle
      have hkpow : 2 ≤ 2 ^ k := by
        have h := (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ k))
        simpa using h
      dsimp [F]
      omega

end D5.S3.Arith.Primes.OeisA369378FermatCovering

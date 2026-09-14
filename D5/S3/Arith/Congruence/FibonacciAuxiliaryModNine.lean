/- GID: D5/S3/Arith/Congruence/FibonacciAuxiliaryModNine
   generality: G
   mirror-B: none(waiver:universal-residue-character)
   mirror-E: none(waiver:all-coprime-six-indices)
   anchors: []
   digest: A multiplicative character modulo twelve determines the actual Fibonacci square modulo nine. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Congruence.FibonacciAuxiliaryModNine

private def characterTable (r : ℕ) : ℤ :=
  if r = 1 ∨ r = 11 then 1 else if r = 5 ∨ r = 7 then -1 else 0

/-- An auxiliary character on the index, not a change of the fixed golden field. -/
def auxiliaryCharacter12 (n : ℕ) : ℤ := characterTable (n % 12)

/-- The actual residue character is multiplicative, including its zero values. -/
theorem auxiliary_character_mul (m n : ℕ) :
    auxiliaryCharacter12 (m * n) = auxiliaryCharacter12 m * auxiliaryCharacter12 n := by
  have table : ∀ a b : Fin 12,
      auxiliaryCharacter12 (a.val * b.val) =
        auxiliaryCharacter12 a.val * auxiliaryCharacter12 b.val := by
    decide +kernel
  have hm : m % 12 < 12 := Nat.mod_lt m (by decide)
  have hn : n % 12 < 12 := Nat.mod_lt n (by decide)
  calc
    auxiliaryCharacter12 (m * n) = auxiliaryCharacter12 ((m % 12) * (n % 12)) := by
      exact congrArg characterTable (Nat.mul_mod m n 12)
    _ = auxiliaryCharacter12 (m % 12) * auxiliaryCharacter12 (n % 12) :=
      table ⟨m % 12, hm⟩ ⟨n % 12, hn⟩
    _ = auxiliaryCharacter12 m * auxiliaryCharacter12 n := by
      simp only [auxiliaryCharacter12, Nat.mod_mod]

private abbrev fibNine (n : ℕ) : ZMod 9 := Nat.fib n

private lemma fibNine_add_two (n : ℕ) :
    fibNine (n + 2) = fibNine n + fibNine (n + 1) := by
  simp only [fibNine, Nat.fib_add_two, Nat.cast_add]

private lemma fibNine_period (n : ℕ) : fibNine (n + 24) = fibNine n := by
  induction n using Nat.twoStepInduction with
  | zero => decide +kernel
  | one => decide +kernel
  | more n h0 h1 =>
    calc
      fibNine ((n + 2) + 24) = fibNine ((n + 24) + 2) := by congr 1; omega
      _ = fibNine (n + 24) + fibNine ((n + 1) + 24) := by
        rw [fibNine_add_two (n + 24)]
        congr 1
        congr 1
        omega
      _ = fibNine n + fibNine (n + 1) := by rw [h0, h1]
      _ = fibNine (n + 2) := (fibNine_add_two n).symm

private lemma fibNine_reduce (n : ℕ) : fibNine n = fibNine (n % 24) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 24
    · rw [Nat.mod_eq_of_lt hn]
    have hsmall : n - 24 < n := by omega
    have hm : (n - 24) % 24 = n % 24 := by omega
    calc
      fibNine n = fibNine ((n - 24) + 24) := by congr 1; omega
      _ = fibNine (n - 24) := fibNine_period (n - 24)
      _ = fibNine ((n - 24) % 24) := ih _ hsmall
      _ = fibNine (n % 24) := by rw [hm]

/-- A universal congruence. The finite table in the proof is exhaustive because
periodicity was proved for every index, rather than assumed as a search cutoff. -/
theorem fibonacci_square_mod_nine (n : ℕ) (hn : n % 6 = 1 ∨ n % 6 = 5) :
    (Nat.fib n : ZMod 9) ^ 2 = 4 - 3 * (auxiliaryCharacter12 n : ZMod 9) := by
  have table : ∀ r : Fin 24, r.val % 6 = 1 ∨ r.val % 6 = 5 →
      fibNine r.val ^ 2 = 4 - 3 * (auxiliaryCharacter12 r.val : ZMod 9) := by
    decide +kernel
  have hr : n % 24 < 24 := Nat.mod_lt n (by decide)
  have h6 : (n % 24) % 6 = 1 ∨ (n % 24) % 6 = 5 := by omega
  have h12 : (n % 24) % 12 = n % 12 := by omega
  have hc : auxiliaryCharacter12 (n % 24) = auxiliaryCharacter12 n :=
    congrArg characterTable h12
  change fibNine n ^ 2 = _
  rw [fibNine_reduce n, ← hc]
  exact table ⟨n % 24, hr⟩ h6

end D5.S3.Arith.Congruence.FibonacciAuxiliaryModNine

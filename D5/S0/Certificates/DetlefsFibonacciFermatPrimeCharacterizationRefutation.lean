/- GID: D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic, mathlib/module/Mathlib.Tactic.NormNum.Prime, mathlib/module/Mathlib.Tactic.ReduceModChar]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.claim; result=D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.result; claim=D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.claim
   digest: Finite certificate at 219781 refutes Detlefs 2014 Fibonacci-Fermat prime characterization. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S0.Certificates.DetlefsFibonacciFermatPrimeCharacterizationRefutation

/-- %F A000040 Conjecture: Sequence = {5 and n <> 5| ( Fibonacci(n) mod n = 1 or Fibonacci(n) mod n = n - 1) and 2^(n-1) mod n = 1}. - _Gary Detlefs_, May 25 2014 -/
def fibTest (n : ℕ) : Prop :=
  Nat.fib n % n = 1 ∨ Nat.fib n % n = n - 1

/-- %F A000040 Conjecture: Sequence = {5 and n <> 5| ( Fibonacci(n) mod n = 1 or Fibonacci(n) mod n = n - 1) and 2^(n-1) mod n = 1}. - _Gary Detlefs_, May 25 2014 -/
def fermatTest (n : ℕ) : Prop :=
  2 ^ (n - 1) % n = 1

/-- %F A000040 Conjecture: Sequence = {5 and n <> 5| ( Fibonacci(n) mod n = 1 or Fibonacci(n) mod n = n - 1) and 2^(n-1) mod n = 1}. - _Gary Detlefs_, May 25 2014 -/
def inDetlefsSet (n : ℕ) : Prop :=
  n = 5 ∨ (n ≠ 5 ∧ fibTest n ∧ fermatTest n)

/-- %F A000040 Conjecture: Sequence = {5 and n <> 5| ( Fibonacci(n) mod n = 1 or Fibonacci(n) mod n = n - 1) and 2^(n-1) mod n = 1}. - _Gary Detlefs_, May 25 2014 -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n → (Nat.Prime n ↔ inDetlefsSet n)

/-- Refutes verbatim: %F A000040 Conjecture: Sequence = {5 and n <> 5| ( Fibonacci(n) mod n = 1 or Fibonacci(n) mod n = n - 1) and 2^(n-1) mod n = 1}. - _Gary Detlefs_, May 25 2014 -/
theorem result : ¬ claim := by
  intro hclaim
  have hFibFast : Nat.fastFib 219781 % 219781 = 1 := by decide
  have hFib : Nat.fib 219781 % 219781 = 1 := by
    rw [← Nat.fastFib_eq]
    exact hFibFast
  have hPowZMod : (2 : ZMod 219781) ^ 219780 = 1 := by
    reduce_mod_char
  have hPow : 2 ^ 219780 % 219781 = 1 := by
    have hCast : ((2 ^ 219780 : ℕ) : ZMod 219781) = ((1 : ℕ) : ZMod 219781) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hPowZMod
    have hMod := (ZMod.natCast_eq_natCast_iff' (2 ^ 219780) 1 219781).mp hCast
    norm_num at hMod ⊢
    exact hMod
  have hFermat : fermatTest 219781 := by
    simpa only [fermatTest, Nat.reduceSub] using hPow
  have hSet : inDetlefsSet 219781 := by
    right
    exact ⟨by decide, Or.inl hFib, hFermat⟩
  have hPrime : Nat.Prime 219781 :=
    (hclaim 219781 (by decide)).mpr hSet
  exact (by norm_num : ¬ Nat.Prime 219781) hPrime

#print axioms fibTest
#print axioms fermatTest
#print axioms inDetlefsSet
#print axioms claim
#print axioms result

end D5.S0.Certificates.DetlefsFibonacciFermatPrimeCharacterizationRefutation

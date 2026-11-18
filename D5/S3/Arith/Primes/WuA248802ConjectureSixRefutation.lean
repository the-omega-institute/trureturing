/- GID: D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/WuA248802ConjectureSixRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq, mathlib/module/Mathlib.Data.Nat.Prime.Defs]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.claim; result=D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.result; claim=D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.claim
   digest: An admissible overlap with House's divisor refutes Wu's full Conjecture 6. -/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option exponentiation.threshold 1000

namespace D5.S3.Arith.Primes.WuA248802ConjectureSixRefutation

/-!
Wu's 2019 Conjecture 6 in OEIS A248802 asserts the value 2383 at 44n+10
outside all five preceding domains. The immutable source and prior-art scope
are recorded in Library/Factorization/wu2019a248802c6.md.

Matthew House's MathOverflow answer and linked divisibility table supply
the progression 274+292j with divisor 1759. The certificate uses its
intersection 3486 = 44*79+10 = 274+292*11, proves admissibility, and applies
Nat.minFac_le_of_dvd. No primality or exact minimum equality is needed.
-/

/-- Domain of Conjecture 1, including parameter zero. -/
def coveredOne (k : ℕ) : Prop := ∃ m : ℕ, k = 10 * m + 2

/-- Domain of Conjecture 2, retaining its modulo-five condition. -/
def coveredTwo (k : ℕ) : Prop := ∃ m : ℕ, k = 36 * m + 16 ∧ m % 5 ≠ 1

/-- Domain of Conjecture 3, retaining its modulo-five condition. -/
def coveredThree (k : ℕ) : Prop := ∃ m : ℕ, k = 84 * m + 22 ∧ m % 5 ≠ 0

/-- Domain of Conjecture 4, recursively excluding the first three domains. -/
def coveredFour (k : ℕ) : Prop :=
  (∃ m : ℕ, k = 58 * m + 26) ∧ ¬ coveredOne k ∧ ¬ coveredTwo k ∧ ¬ coveredThree k

/-- Domain of Conjecture 5, retaining its modulo-five condition. -/
def coveredFive (k : ℕ) : Prop := ∃ m : ℕ, k = 138 * m + 6 ∧ m % 5 ≠ 2

/-- The full source claim, with the original natural least-prime-factor carrier. -/
def claim : Prop :=
  ∀ n : ℕ, ¬ coveredOne (44 * n + 10) → ¬ coveredTwo (44 * n + 10) →
    ¬ coveredThree (44 * n + 10) → ¬ coveredFour (44 * n + 10) → ¬ coveredFive (44 * n + 10) →
    Nat.minFac (2 ^ (2 ^ (44 * n + 10) + 2) + 3) = 2383

private theorem divisor_of_inner_residue (e : ℕ) (hi : e % 879 = 718) :
    1759 ∣ (2 : ℕ) ^ (e + 2) + 3 := by
  have h879 : (2 : ℕ) ^ 879 ≡ 1 [MOD 1759] := by decide
  have h720 : (2 : ℕ) ^ 720 ≡ 1756 [MOD 1759] := by decide
  have he : e + 2 = 720 + 879 * (e / 879) := by
    have h := Nat.mod_add_div e 879
    omega
  have houter : (2 : ℕ) ^ (e + 2) ≡ 1756 [MOD 1759] := by
    rw [he, pow_add, pow_mul]
    simpa only [one_pow, mul_one] using h720.mul (h879.pow (e / 879))
  exact Nat.modEq_zero_iff_dvd.mp ((houter.add_right 3).trans (by decide))

private theorem minFac_ne_of_dvd (x : ℕ) (hd : 1759 ∣ x) : Nat.minFac x ≠ 2383 :=
  ne_of_lt ((Nat.minFac_le_of_dvd (by decide : 2 ≤ 1759) hd).trans_lt
    (by decide : 1759 < 2383))

/-- The admissible witness n = 79 refutes the entire conditional universal claim. -/
theorem result : ¬ claim := by
  have hc1 : ¬ coveredOne 3486 := by rintro ⟨m, hm⟩; omega
  have hc2 : ¬ coveredTwo 3486 := by rintro ⟨m, hm, _⟩; omega
  have hc3 : ¬ coveredThree 3486 := by rintro ⟨m, hm, _⟩; omega
  have hc4 : ¬ coveredFour 3486 := by rintro ⟨⟨m, hm⟩, _⟩; omega
  have hc5 : ¬ coveredFive 3486 := by rintro ⟨m, hm, _⟩; omega
  have h292 : (2 : ℕ) ^ 292 ≡ 1 [MOD 879] := by decide
  have h274 : (2 : ℕ) ^ 274 ≡ 718 [MOD 879] := by decide
  have hinner : (2 : ℕ) ^ (44 * 79 + 10) ≡ 718 [MOD 879] := by
    have h := h274.mul (h292.pow 11)
    simpa only [one_pow, mul_one, ← pow_mul, ← pow_add] using h
  have hd : 1759 ∣ (2 : ℕ) ^ (2 ^ (44 * 79 + 10) + 2) + 3 :=
    divisor_of_inner_residue (2 ^ (44 * 79 + 10)) hinner
  intro hclaim
  exact minFac_ne_of_dvd _ hd (hclaim 79 hc1 hc2 hc3 hc4 hc5)

#print axioms claim
#print axioms result

end D5.S3.Arith.Primes.WuA248802ConjectureSixRefutation

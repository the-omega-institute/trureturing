/- GID: D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Order.Lattice.Nat, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.NormNum.Prime]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.claim; result=D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.result; claim=D5/S0/Certificates/MurthyLeastPrimePrefixSuffixRefutation.claim
   digest: The value a(1) = 11 refutes Murthy's conjectured suffix bound for OEIS A018800. -/

import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S0.Certificates.MurthyLeastPrimePrefixSuffixRefutation

/-!
OEIS A018800 defines `a(n)` as the smallest prime whose decimal expansion
begins with the decimal expansion of `n`.  The interval
`[n * 10^m, (n + 1) * 10^m)` expresses that prefix relation, including
`m = 0` so that a prime `n` is its own least prefix prime.

Murthy's conjecture concerns a nonempty appended suffix, hence `m >= 1`.
At `n = 1`, the least prefix prime is `11 = 1 * 10 + 1`, whose suffix is
not strictly smaller than the prefix.
-/

/-- The least prime in any decimal-prefix interval belonging to `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ |
    Nat.Prime p ∧
      ∃ m : ℕ, n * 10 ^ m ≤ p ∧ p < (n + 1) * 10 ^ m}

/-- Murthy's claimed strict bound on every nonempty appended suffix. -/
def claim : Prop :=
  ∀ n m k : ℕ,
    1 ≤ n →
    1 ≤ m →
    k < 10 ^ m →
    a n = n * 10 ^ m + k →
    k < n

/-- The value `a(1) = 11` refutes the claimed strict suffix bound. -/
theorem result : ¬ claim := by
  let prefixPrimes : Set ℕ := {p : ℕ |
    Nat.Prime p ∧
      ∃ m : ℕ, 1 * 10 ^ m ≤ p ∧ p < (1 + 1) * 10 ^ m}
  have h11_mem : 11 ∈ prefixPrimes := by
    change Nat.Prime 11 ∧
      ∃ m : ℕ, 1 * 10 ^ m ≤ 11 ∧ 11 < (1 + 1) * 10 ^ m
    refine ⟨by norm_num, 1, ?_⟩
    norm_num
  have ha_one : a 1 = 11 := by
    change sInf prefixPrimes = 11
    apply le_antisymm
    · exact Nat.sInf_le h11_mem
    · have hleast_mem := Nat.sInf_mem (s := prefixPrimes) ⟨11, h11_mem⟩
      rcases hleast_mem with ⟨hprime, m, hlower, hupper⟩
      by_cases hm : m = 0
      · subst m
        norm_num at hlower hupper
        have hsInf : sInf prefixPrimes = 1 := by
          omega
        rw [hsInf] at hprime
        norm_num at hprime
      · have hm_one : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        have hten : 10 ≤ 10 ^ m := by
          simpa only [pow_one] using
            (Nat.pow_le_pow_right (by norm_num : 0 < 10) hm_one)
        have hsInf_ne : sInf prefixPrimes ≠ 10 := by
          intro hsInf
          rw [hsInf] at hprime
          norm_num at hprime
        have hsInf_ten : 10 ≤ sInf prefixPrimes := by
          exact hten.trans (by simpa only [one_mul] using hlower)
        omega
  intro hclaim
  have hfalse := hclaim 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num [ha_one])
  omega

#print axioms a
#print axioms claim
#print axioms result

end D5.S0.Certificates.MurthyLeastPrimePrefixSuffixRefutation

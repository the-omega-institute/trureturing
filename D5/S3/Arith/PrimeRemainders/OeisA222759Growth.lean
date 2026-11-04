/- GID: D5/S3/Arith/PrimeRemainders/OeisA222759Growth
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeRemainders/OeisA222759Growth
   mirror-E: none(waiver:noncomputational-universal-result)
   anchors: []
   utility: none
   digest: The nested prime threshold supplies k distinct cubic-remainder witnesses. -/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.PrimeRemainders.OeisA222759Growth

/-- The one-based prime enumeration on positive indices. -/
noncomputable def P (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)

/-- The literal least nonnegative binomial remainder modulo the cube. -/
def cubicRemainder (n q : ℕ) : ℕ := Nat.choose (n * q) q % q ^ 3

/-- The complete first growth assertion of OEIS A222759, with k distinct witnesses. -/
theorem result (k n : ℕ) (hk : 3 ≤ k) (hn : 1 ≤ n)
    (hthreshold : P (P k ^ 3) ≤ n) :
    ∃ q : Fin k → ℕ, Function.Injective q ∧
      ∀ i : Fin k, 0 < q i ∧ Nat.Prime (q i) ∧ cubicRemainder n (q i) ≠ n := by
  have hPk : Nat.Prime (P k) := Nat.prime_nth_prime (k - 1)
  have hm : 0 < P k ^ 3 := pow_pos hPk.pos _
  have hindex := Nat.add_two_le_nth_prime (P k ^ 3 - 1)
  change P k ^ 3 - 1 + 2 ≤ P (P k ^ 3) at hindex
  have hcube : P k ^ 3 < n := by omega
  refine ⟨fun i => Nat.nth Nat.Prime i.val, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    exact Nat.nth_injective Nat.infinite_setOfPred_prime hij
  · intro i
    have hq : Nat.Prime (Nat.nth Nat.Prime i.val) := Nat.prime_nth_prime i.val
    have hle : Nat.nth Nat.Prime i.val ≤ P k :=
      Nat.nth_monotone Nat.infinite_setOfPred_prime (by omega : i.val ≤ k - 1)
    refine ⟨hq.pos, hq, ?_⟩
    exact ne_of_lt ((Nat.mod_lt _ (pow_pos hq.pos 3)).trans
      ((pow_le_pow_left' hle 3).trans_lt hcube))

end D5.S3.Arith.PrimeRemainders.OeisA222759Growth

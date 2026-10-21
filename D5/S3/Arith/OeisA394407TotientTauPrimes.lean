/- GID: D5/S3/Arith/OeisA394407TotientTauPrimes
   generality: G
   mirror-B: D5/B/S3/Arith/OeisA394407TotientTauPrimes
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every prime other than three first attains its totient-to-divisor-count ratio. -/

/-
ratio: proof_shape: bind-only (definition); consumers: IsTerm, result.
IsTerm: proof_shape: bind-only (definition); consumers: claim, result.
claim: proof_shape: bind-only (definition); consumer: result.
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#18591; Proved).
Direct frozen dependencies: none, for every declaration; no D5 imports.
The proof uses Mathlib's totient and divisor facts with rational normalization.
The definitions reproduce the expressions in OEIS A394407 and #18591.
Utility is none: the named declarations define symbolic objects or prove a universal
statement; the two source examples are fidelity checks, not a finite settlement.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19902.
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S3.Arith.OeisA394407TotientTauPrimes

/-- `phi(m)/tau(m)` as a rational number. -/
def ratio (m : ℕ) : ℚ := (Nat.totient m : ℚ) / (m.divisors.card : ℚ)

/-- `k` is a term of A394407: no smaller positive `m` has the same value of `phi/tau`. -/
def IsTerm (k : ℕ) : Prop := 0 < k ∧ ∀ m : ℕ, 0 < m → m < k → ratio m ≠ ratio k

/-- The conjecture of A394407: every prime `p ≠ 3` is a term. -/
def claim : Prop := ∀ p : ℕ, p.Prime → p ≠ 3 → IsTerm p

/-! Fidelity checks (not part of the conventions): the two examples of the entry. -/

example : ratio 14 = 3 / 2 := by
  simp only [ratio]
  rw [show Nat.totient 14 = 6 by decide, show (Nat.divisors 14).card = 4 by decide]
  norm_num

example : ratio 1 = ratio 3 := by
  simp only [ratio]
  rw [show Nat.totient 3 = 2 by decide, show (Nat.divisors 3).card = 2 by decide]
  norm_num


set_option maxHeartbeats 2000000 in
/-- Every prime other than three is a new value of the totient/divisor-count ratio. -/
theorem result : claim := by
  intro p hp hp3
  have hcard : p.divisors.card = 2 := by
    rw [hp.divisors]
    simp [Ne.symm hp.ne_one]
  have hratio : ratio p = ((p : ℚ) - 1) / 2 := by
    rw [ratio, Nat.totient_prime hp, hcard, Nat.cast_sub hp.one_le]
    norm_num
  refine ⟨hp.pos, ?_⟩
  intro m hm hmp heq
  rw [hratio] at heq
  by_cases hm1 : m = 1
  · subst m
    norm_num [ratio] at heq
    have hpQ : (p : ℚ) = 3 := by linarith
    exact hp3 (by exact_mod_cast hpQ)
  · have hm2 : 1 < m := Nat.lt_of_le_of_ne hm (Ne.symm hm1)
    have htwo : 2 ≤ m.divisors.card := by
      apply Finset.one_lt_card.mpr
      exact ⟨1, Nat.one_mem_divisors.mpr (Nat.ne_of_gt hm),
        m, Nat.mem_divisors_self m (Nat.ne_of_gt hm), Ne.symm hm1⟩
    have hden2 : (2 : ℚ) ≤ (m.divisors.card : ℚ) := Nat.ofNat_le_cast.mpr htwo
    have hphi : (Nat.totient m : ℚ) < (m : ℚ) := by
      exact_mod_cast Nat.totient_lt m hm2
    have hmpQ : (m : ℚ) + 1 ≤ (p : ℚ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr hmp)
    have hbound : ratio m ≤ (Nat.totient m : ℚ) / 2 := by
      dsimp [ratio]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) zero_lt_two hden2
    have hlt : (Nat.totient m : ℚ) / 2 < ((p : ℚ) - 1) / 2 := by linarith
    linarith

end D5.S3.Arith.OeisA394407TotientTauPrimes

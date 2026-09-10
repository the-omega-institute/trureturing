/- GID: D5/S3/Arith/IsolatedQuotientRemainder
   generality: I
   mirror-B: D5/B/S3/Arith/IsolatedQuotientRemainder
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: An isolated quotient-remainder equality above 24 forces the successor to be prime. -/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.IsolatedQuotientRemainder

/-- The quotient-remainder equality holds only at the endpoints of the natural interval. -/
def P (t : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ t → (t % k = ((t - k) / k) % k → k = 1 ∨ k = t)

private theorem remainder_of_decomposition (t k q r : ℕ) (hk : 0 < k)
    (hq : 1 ≤ q) (hr : r < k) (ht : t = q * k + r)
    (hqr : (q - 1) % k = r) : t % k = ((t - k) / k) % k := by
  have hq' : q = (q - 1) + 1 := by omega
  have hsub : t - k = r + (q - 1) * k := by
    rw [hq', Nat.add_mul, one_mul] at ht
    omega
  rw [hsub, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hr, zero_add, hqr]
  simp only [ht, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt hr]

private theorem unequal_factor_witness (t a b : ℕ) (ha : 2 ≤ a) (hab : a < b)
    (ht : t + 1 = a * b) :
    ∃ k, 1 < k ∧ k < t ∧ t % k = ((t - k) / k) % k := by
  let k := b - 1
  have hk : 1 < k := by omega
  have hb : b = k + 1 := by omega
  have ha' : a - 1 + 1 = a := by omega
  have hdecomp : t = a * k + (a - 1) := by
    rw [hb] at ht
    nlinarith
  have hkt : k < t := by
    nlinarith [Nat.mul_le_mul_right k ha]
  refine ⟨k, hk, hkt, remainder_of_decomposition t k a (a - 1) (by omega)
    (by omega) (by omega) hdecomp ?_⟩
  exact Nat.mod_eq_of_lt (by omega)

private theorem square_factor_witness (t u : ℕ) (ht : 24 < t)
    (hsq : t + 1 = u * u) :
    ∃ k, 1 < k ∧ k < t ∧ t % k = ((t - k) / k) % k := by
  have hu : 6 ≤ u := by
    by_contra h
    have hu5 : u ≤ 5 := by omega
    have := Nat.mul_self_le_mul_self hu5
    omega
  let k := u - 2
  have hk : 3 < k := by omega
  have hu' : u = k + 2 := by omega
  have hdecomp : t = (u + 2) * k + 3 := by
    rw [hu'] at hsq ⊢
    nlinarith
  have hkt : k < t := by
    nlinarith [Nat.mul_le_mul_right k hu]
  refine ⟨k, by omega, hkt, remainder_of_decomposition t k (u + 2) 3
    (by omega) (by omega) hk hdecomp ?_⟩
  have hq : u + 2 - 1 = 3 + k := by omega
  rw [hq, Nat.add_mod_right, Nat.mod_eq_of_lt hk]

/-- For every isolated value greater than 24 in A375007, its successor is prime. -/
theorem a375007_prime (t : ℕ) (ht : 24 < t) (h : P t) : Nat.Prime (t + 1) := by
  by_contra hp
  let a := Nat.minFac (t + 1)
  let b := (t + 1) / a
  have ha : 2 ≤ a := (Nat.minFac_prime (by omega : t + 1 ≠ 1)).two_le
  have hab : a ≤ b := Nat.minFac_le_div (by omega) hp
  have hprod : t + 1 = a * b := (Nat.mul_div_cancel' (Nat.minFac_dvd (t + 1))).symm
  have hw : ∃ k, 1 < k ∧ k < t ∧ t % k = ((t - k) / k) % k := by
    rcases lt_or_eq_of_le hab with hlt | heq
    · exact unequal_factor_witness t a b ha hlt hprod
    · exact square_factor_witness t a ht (by simpa only [← heq] using hprod)
  obtain ⟨k, hk, hkt, heq⟩ := hw
  rcases h k (by omega) (by omega) heq with h1 | ht'
  · omega
  · omega

end D5.S3.Arith.IsolatedQuotientRemainder

/- GID: D5/S1/Recurrence/MarcusTentMapSuborder
   generality: G
   mirror-B: D5/B/S1/Recurrence/MarcusTentMapSuborder
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Marcus's tent-map cycle length is the signed suborder of two. -/

import Mathlib.FieldTheory.Finite.Basic

namespace D5.S1.Recurrence.MarcusTentMapSuborder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Numerator action of the tent map `x ↦ 1 - |2*x - 1|` at `x = k/N`.
For `N > 0` and `k ≤ N`, the branch `2*k ≤ N` gives numerator `2*k`,
and the branch `N < 2*k` gives numerator `2*N - 2*k`. The latter natural
subtraction is not truncated when `k ≤ N`; dividing either numerator by
`N` in the rationals recovers the corresponding branch of the tent map. -/
def tent (N k : ℕ) : ℕ := if 2 * k ≤ N then 2 * k else 2 * N - 2 * k

private theorem orbit_invariant (N : ℕ) (hN : 2 ≤ N) (m : ℕ) :
    (tent N)^[m] 2 ≤ N ∧ Even ((tent N)^[m] 2) ∧
      (((tent N)^[m] 2 : ℕ) : ZMod N) = 2 ^ (m + 1) ∨
      (tent N)^[m] 2 ≤ N ∧ Even ((tent N)^[m] 2) ∧
      (((tent N)^[m] 2 : ℕ) : ZMod N) = -(2 ^ (m + 1)) := by
  induction m with
  | zero =>
      left
      simpa using (show 2 ≤ N ∧ Even (2 : ℕ) ∧ (2 : ZMod N) = 2 from
        ⟨hN, by decide, rfl⟩)
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      generalize hk : (tent N)^[m] 2 = k at *
      rcases ih with ⟨hb, he, hs⟩ | ⟨hb, he, hs⟩ <;>
        unfold tent <;> split_ifs with hc
      · left
        refine ⟨hc, even_two_mul _, ?_⟩
        push_cast
        rw [hs, pow_succ]
        ring
      · right
        refine ⟨by omega, ?_, ?_⟩
        · exact ⟨N - k, by omega⟩
        · rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_mul]
          norm_num
          rw [hs, pow_succ]
          ring
      · right
        refine ⟨hc, even_two_mul _, ?_⟩
        push_cast
        rw [hs, pow_succ]
        ring
      · left
        refine ⟨by omega, ?_, ?_⟩
        · exact ⟨N - k, by omega⟩
        · rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_mul]
          norm_num
          rw [hs, pow_succ]
          ring

theorem result (n : ℕ) (hn : 0 < n) :
    IsLeast {m : ℕ | 0 < m ∧ (2 ^ m ≡ 1 [MOD 2 * n + 1] ∨
      2 ^ m ≡ 2 * n [MOD 2 * n + 1])}
      (Function.minimalPeriod (tent (2 * n + 1)) 2) := by
  have hN : 2 < 2 * n + 1 := by omega
  have hcop : Nat.Coprime 2 (2 * n + 1) :=
    Nat.coprime_two_left.mpr ⟨n, rfl⟩
  have hu : IsUnit (2 : ZMod (2 * n + 1)) :=
    (ZMod.isUnit_iff_coprime 2 (2 * n + 1)).mpr hcop
  have hneg : ((2 * n : ℕ) : ZMod (2 * n + 1)) = -1 := by
    have h := ZMod.natCast_self (2 * n + 1)
    push_cast at h ⊢
    linear_combination h
  have unique (k : ℕ) (hb : k ≤ 2 * n + 1) (he : Even k)
      (hs : (k : ZMod (2 * n + 1)) = 2 ∨ (k : ZMod (2 * n + 1)) = -2) :
      k = 2 := by
    have hk : k < 2 * n + 1 := by
      rcases he with ⟨a, ha⟩
      omega
    rcases hs with hs | hs
    · have hm : k % (2 * n + 1) = 2 % (2 * n + 1) :=
        (ZMod.natCast_eq_natCast_iff' k 2 (2 * n + 1)).mp (by simpa using hs)
      simpa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hN] using hm
    · have hr : (((2 * n + 1) - 2 : ℕ) : ZMod (2 * n + 1)) = -2 := by
        rw [Nat.cast_sub (by omega)]
        simp
      have hm : k % (2 * n + 1) = (2 * n + 1 - 2) % (2 * n + 1) :=
        (ZMod.natCast_eq_natCast_iff' k (2 * n + 1 - 2) (2 * n + 1)).mp
          (hs.trans hr.symm)
      rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)] at hm
      rcases he with ⟨a, ha⟩
      omega
  have periodic_iff (m : ℕ) :
      Function.IsPeriodicPt (tent (2 * n + 1)) m 2 ↔
        (2 ^ m ≡ 1 [MOD 2 * n + 1] ∨ 2 ^ m ≡ 2 * n [MOD 2 * n + 1]) := by
    change (tent (2 * n + 1))^[m] 2 = 2 ↔ _
    simp only [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_ofNat, hneg]
    have hi := orbit_invariant (2 * n + 1) hN.le m
    constructor
    · intro hm
      rcases hi with ⟨hb, he, hs⟩ | ⟨hb, he, hs⟩
      · left
        rw [hm] at hs
        norm_num at hs
        apply hu.mul_left_cancel
        rw [pow_succ] at hs
        linear_combination -hs
      · right
        rw [hm] at hs
        norm_num at hs
        apply hu.mul_left_cancel
        rw [pow_succ] at hs
        linear_combination hs
    · intro hm
      rcases hi with ⟨hb, he, hs⟩ | ⟨hb, he, hs⟩
      · apply unique _ hb he
        rcases hm with hm | hm
        · left
          rw [pow_succ, hm] at hs
          simpa using hs
        · right
          rw [pow_succ, hm] at hs
          simpa using hs
      · apply unique _ hb he
        rcases hm with hm | hm
        · right
          rw [pow_succ, hm] at hs
          simpa using hs
        · left
          rw [pow_succ, hm] at hs
          simpa using hs
  have hperiod : Function.IsPeriodicPt (tent (2 * n + 1)) (Nat.totient (2 * n + 1)) 2 :=
    (periodic_iff _).mpr (Or.inl (Nat.ModEq.pow_totient hcop))
  refine ⟨⟨hperiod.minimalPeriod_pos (Nat.totient_pos.mpr (by omega)),
    (periodic_iff _).mp (Function.isPeriodicPt_minimalPeriod _ _)⟩, ?_⟩
  intro m hm
  exact ((periodic_iff m).mpr hm.2).minimalPeriod_le hm.1


end D5.S1.Recurrence.MarcusTentMapSuborder

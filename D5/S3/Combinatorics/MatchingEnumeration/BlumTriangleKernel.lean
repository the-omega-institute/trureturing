/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangleKernel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangleKernel
   mirror-E: none(waiver:general-kernel-recurrence)
   anchors: [mathlib/module/Mathlib.Algebra.CharP.Two, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Rectangle sums solve the reduced-row kernel recurrence for every order. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleKernel

open Finset

/-- Every zero-extended solution of the reduced odd-row equations is the sum of the
explicit rectangle vectors, with its diagonal entries as coefficients. -/
theorem reduced_kernel_expansion {K : Type*} [CommRing K] [CharP K 2]
    (k : ℕ) (f : ℕ → ℕ → K)
    (hsupport : ∀ a b, ¬ (a < 2 * k ∧ a ≤ b ∧ a + b < 4 * k) → f a b = 0)
    (heq : ∀ a b, a < 2 * k → a ≤ b → a + b + 1 < 4 * k →
      (if a % 2 = 0 ∧ b = 2 * k - 1 then
        f a (b + 1) + f (a + 1) (b + 1)
      else f a b + f (a + 1) b + f a (b + 1) + f (a + 1) (b + 1)) = 0)
    (a b : ℕ) :
    f a b = ∑ j : Fin (2 * k),
      if a ≤ j.val ∧ j.val ≤ b ∧
          b ≤ (if j.val % 2 = 0 then 2 * k - 1 else 4 * k - 1 - j.val)
      then f j.val j.val else 0 := by
  classical
  let c := 2 * k - 1
  let rightEnd : ℕ → ℕ := fun j => if j % 2 = 0 then c else 4 * k - 1 - j
  let g : ℕ → ℕ → K := fun a b => f a b + f (a + 1) b
  have adjacent (r s : ℕ) (hr : r < 2 * k) (hrs : r ≤ s)
      (hb : r + s + 1 < 4 * k) (hn : ¬ (r % 2 = 0 ∧ s = c)) :
      g r s = g r (s + 1) := by
    have h := heq r s hr hrs hb
    change (if r % 2 = 0 ∧ s = c then _ else _) = 0 at h
    rw [if_neg hn] at h
    apply CharTwo.add_eq_zero.mp
    simpa only [g, add_assoc] using h
  have leftConstant (r : ℕ) (hr : r < 2 * k) :
      ∀ s, r ≤ s → r + s < 4 * k → (r % 2 ≠ 0 ∨ s ≤ c) → g r s = f r r := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro hrs hb hleft
      by_cases he : s = r
      · subst s
        have hz : f (r + 1) r = 0 := hsupport _ _ (by omega)
        simp [g, hz]
      · have hsr : r ≤ s - 1 := by omega
        have hpred : s - 1 < s := by omega
        have hnext : s - 1 + 1 = s := by omega
        have hnot : ¬ (r % 2 = 0 ∧ s - 1 = c) := by
          rcases hleft with hleft | hleft <;> omega
        have hs := adjacent r (s - 1) hr hsr (by omega) hnot
        rw [hnext] at hs
        rw [← hs]
        apply ih (s - 1) hpred hsr (by omega)
        rcases hleft with hleft | hleft
        · exact Or.inl hleft
        · exact Or.inr (by omega)
  have rightZero (r : ℕ) (hr : r < 2 * k) (heven : r % 2 = 0) :
      ∀ s, c < s → r + s < 4 * k → g r s = 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro hright hb
      have hrc : r ≤ c := by dsimp [c]; omega
      by_cases he : s = c + 1
      · subst s
        have h := heq r c hr hrc (by omega)
        simpa only [heven, c, and_self, if_pos, g] using h
      · have hpred : s - 1 < s := by omega
        have hnext : s - 1 + 1 = s := by omega
        have hs := adjacent r (s - 1) hr (by omega) (by omega) (by omega)
        rw [hnext] at hs
        rw [← hs]
        exact ih (s - 1) hpred (by omega) (by omega)
  have rows (r s : ℕ) :
      g r s = if r < 2 * k ∧ r ≤ s ∧ s ≤ rightEnd r then f r r else 0 := by
    by_cases hdom : r < 2 * k ∧ r ≤ s ∧ r + s < 4 * k
    · rcases hdom with ⟨hr, hrs, hb⟩
      by_cases heven : r % 2 = 0
      · by_cases hright : c < s
        · rw [rightZero r hr heven s hright hb]
          have hn : ¬ (r < 2 * k ∧ r ≤ s ∧ s ≤ rightEnd r) := by
            simp only [rightEnd, if_pos heven]
            omega
          rw [if_neg hn]
        · rw [leftConstant r hr s hrs hb (Or.inr (by omega))]
          have hc : s ≤ c := by omega
          simp [rightEnd, heven, hr, hrs, hc]
      · rw [leftConstant r hr s hrs hb (Or.inl heven)]
        have hend : s ≤ 4 * k - 1 - r := by omega
        simp [rightEnd, heven, hr, hrs, hend]
    · have hz : f r s = 0 := hsupport r s hdom
      have hz' : f (r + 1) s = 0 := hsupport _ _ (by omega)
      have hn : ¬ (r < 2 * k ∧ r ≤ s ∧ s ≤ rightEnd r) := by
        dsimp [rightEnd, c]
        split_ifs <;> omega
      simp [g, hz, hz', hn]
  let synthesis : ℕ → ℕ → K := fun r s => ∑ j : Fin (2 * k),
    if r ≤ j.val ∧ j.val ≤ s ∧ s ≤ rightEnd j.val then f j.val j.val else 0
  have outside (r s : ℕ) (hr : 2 * k ≤ r) : synthesis r s = 0 := by
    apply sum_eq_zero
    intro j _
    have hj := j.isLt
    have hn : ¬ (r ≤ j.val ∧ j.val ≤ s ∧ s ≤ rightEnd j.val) := by omega
    exact if_neg hn
  have difference (r s : ℕ) : synthesis r s + synthesis (r + 1) s = g r s := by
    by_cases hr : r < 2 * k
    · let i : Fin (2 * k) := ⟨r, hr⟩
      change (∑ j : Fin (2 * k), _) + (∑ j : Fin (2 * k), _) = _
      rw [← sum_add_distrib, sum_eq_single i]
      · rw [rows]
        simp [i, hr]
      · intro j _ hji
        have hjr : j.val ≠ r := by
          intro h
          exact hji (Fin.ext h)
        have hle : r ≤ j.val ↔ r + 1 ≤ j.val := by omega
        simp only [hle]
        exact CharTwo.add_self_eq_zero _
      · simp
    · have hlarge : 2 * k ≤ r := by omega
      rw [outside r s hlarge, outside (r + 1) s (by omega), zero_add]
      have hz : f r s = 0 := hsupport _ _ (by omega)
      have hz' : f (r + 1) s = 0 := hsupport _ _ (by omega)
      simp [g, hz, hz']
  have recover : ∀ d r, 2 * k ≤ r + d → ∀ s, f r s = synthesis r s := by
    intro d
    induction d with
    | zero =>
      intro r hr s
      have hz : f r s = 0 := hsupport _ _ (by omega)
      rw [hz, outside r s (by omega)]
    | succ d ih =>
      intro r hr s
      have hlower := ih (r + 1) (by omega) s
      have h := difference r s
      change synthesis r s + synthesis (r + 1) s = f r s + f (r + 1) s at h
      rw [hlower] at h
      exact (add_right_cancel h).symm
  exact recover (2 * k) a (by omega) b

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleKernel

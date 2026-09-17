/- GID: D5/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/SelfReferentialDoublingFirstOccurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: First occurrence thresholds in Alkan's self-referential doubling recurrence. -/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# First occurrences in a self-referential doubling recurrence

The value at index zero is a sentinel used only to totalize the recurrence;
the source sequence starts at index one.
-/

namespace D5.S1.Recurrence.Invariants.SelfReferentialDoublingFirstOccurrence

/-- Alkan's sequence A335901, totalized at index zero by the sentinel value one. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * a ((n + 1) / a (n + 1))
termination_by n => n
decreasing_by
  · omega
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

/-- A117261 in its recurrence form. -/
def T : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 ^ r * T r + 1

private theorem block_invariant (r : ℕ) :
    a (T r) = 2 ^ r ∧
      ∀ n, T r ≤ n → n < T (r + 1) →
        (a n = (if r = 0 then 0 else 2 ^ (r - 1)) ∨ a n = 2 ^ r) ∧
          (a n = (if r = 0 then 0 else 2 ^ (r - 1)) →
            n < (if r = 0 then 0 else 2 ^ (r - 1)) * T r) := by
  have a_pos (n : ℕ) : 0 < a n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        cases n with
        | zero => simp [a]
        | succ n =>
            cases n with
            | zero => simp [a]
            | succ n =>
                rw [a]
                exact Nat.mul_pos (by omega) (ih _
                  (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)))
  have T_pos (j : ℕ) : 0 < T j := by
    induction j with
    | zero => simp [T]
    | succ j ih => simp [T]
  have a_step (n : ℕ) (hn : 2 ≤ n) :
      a n = 2 * a ((n - 1) / a (n - 1)) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show 2 + j = j + 2 by omega]
    simp [a]
  induction r using Nat.twoStepInduction with
  | zero =>
      constructor
      · simp [T, a]
      · intro n hn hn'
        have hn_eq : n = 1 := by
          simp [T] at hn hn'
          omega
        subst n
        simp [a]
  | one =>
      constructor
      · simp [T, a]
      · intro n hn hn'
        have hn_cases : n = 2 ∨ n = 3 ∨ n = 4 := by
          simp [T] at hn hn'
          omega
        rcases hn_cases with rfl | rfl | rfl <;> simp [a, T]
  | more r hr hr1 =>
      have hprev_mem := hr1.2 (2 ^ (r + 1) * T (r + 1)) (by
        have hp : 1 ≤ 2 ^ (r + 1) := one_le_pow₀ (by omega)
        nlinarith [T_pos (r + 1)]) (by simp [T])
      simp only [if_neg (show r + 1 ≠ 0 by omega), Nat.add_sub_cancel] at hprev_mem
      have hprev : a (2 ^ (r + 1) * T (r + 1)) = 2 ^ (r + 1) := by
        rcases hprev_mem.1 with hlow | hupp
        · have hcut := hprev_mem.2 hlow
          rw [pow_succ] at hcut
          nlinarith [T_pos (r + 1), show 0 < 2 ^ r by positivity]
        · exact hupp
      have hstart : a (T (r + 2)) = 2 ^ (r + 2) := by
        rw [a_step (T (r + 2)) (by
          rw [show T (r + 2) = 2 ^ (r + 1) * T (r + 1) + 1 by simp [T]]
          exact Nat.succ_le_succ (Nat.mul_pos (by positivity) (T_pos (r + 1))))]
        have hpred : T (r + 2) - 1 = 2 ^ (r + 1) * T (r + 1) := by simp [T]
        rw [hpred, hprev]
        have hdiv : (2 ^ (r + 1) * T (r + 1)) / 2 ^ (r + 1) = T (r + 1) := by
          exact Nat.mul_div_right (T (r + 1)) (by positivity)
        rw [hdiv, hr1.1]
        simp [pow_succ, Nat.mul_comm]
      constructor
      · simpa only [Nat.add_assoc] using hstart
      · simp only [if_neg (show r + 2 ≠ 0 by omega),
            show r + 2 - 1 = r + 1 by omega]
        have hTexpand :
            T (r + 2) = (2 ^ (r + 1) * 2 ^ r) * T r + 2 ^ (r + 1) + 1 := by
          simp [T]
          ring
        have hspan : 2 ^ (r + 2) * T r ≤ T (r + 2) := by
          rcases Nat.eq_zero_or_pos r with rfl | hrpos
          · simp [T]
          · rw [hTexpand]
            have hcoef : 2 ^ (r + 2) ≤ 2 ^ (r + 1) * 2 ^ r := by
              rw [← pow_add]
              exact pow_le_pow_right' (by omega) (by omega)
            exact (Nat.mul_le_mul_right (T r) hcoef).trans (by omega)
        have hcutspan :
            (2 ^ (r - 1) * T r) * 2 ^ (r + 2) ≤ T (r + 2) := by
          rcases Nat.eq_zero_or_pos r with rfl | hrpos
          · simp [T]
          · rw [hTexpand]
            have hcoef :
                (2 ^ (r - 1) * T r) * 2 ^ (r + 2) =
                  (2 ^ (r + 1) * 2 ^ r) * T r := by
              calc
                (2 ^ (r - 1) * T r) * 2 ^ (r + 2) =
                    (2 ^ (r - 1) * 2 ^ (r + 2)) * T r := by ring
                _ = 2 ^ ((r - 1) + (r + 2)) * T r := by
                  rw [(pow_add (2 : ℕ) (r - 1) (r + 2)).symm]
                _ = 2 ^ ((r + 1) + r) * T r := by
                  rw [show (r - 1) + (r + 2) = (r + 1) + r by omega]
                _ = (2 ^ (r + 1) * 2 ^ r) * T r := by rw [pow_add]
            rw [hcoef]
            omega
        intro n hn
        induction n, hn using Nat.le_induction with
        | base =>
            intro _
            refine ⟨Or.inr hstart, ?_⟩
            intro hlow
            have hpow_lt : 2 ^ (r + 1) < 2 ^ (r + 2) := by
              simp only [pow_succ]
              have hp : 0 < 2 ^ r := by positivity
              omega
            omega
        | succ n hn ih =>
            intro hnext_upper
            have hn_upper : n < T (r + 2 + 1) := by omega
            have hn_mem := ih hn_upper
            have hden_pos : 0 < a n := a_pos n
            have hpow_le : 2 ^ (r + 1) ≤ 2 ^ (r + 2) := by
              simp only [pow_succ]
              have hp : 0 < 2 ^ r := by positivity
              omega
            have hden_le : a n ≤ 2 ^ (r + 2) := by
              rcases hn_mem.1 with h | h
              · exact h.le.trans hpow_le
              · exact h.le
            have hq_upper : n / a n < T (r + 2) := by
              rcases hn_mem.1 with hlow | hupp
              · rw [hlow]
                apply (Nat.div_lt_iff_lt_mul (by positivity)).2
                simpa [Nat.mul_comm] using hn_mem.2 hlow
              · rw [hupp]
                apply (Nat.div_lt_iff_lt_mul (by positivity)).2
                have hn_bound : n < 2 ^ (r + 2) * T (r + 2) := by
                  rw [show T (r + 2 + 1) = 2 ^ (r + 2) * T (r + 2) + 1 by simp [T]] at hnext_upper
                  omega
                simpa [Nat.mul_comm] using hn_bound
            have hq_lower : T r ≤ n / a n := by
              apply (Nat.le_div_iff_mul_le hden_pos).2
              calc
                T r * a n ≤ T r * 2 ^ (r + 2) := Nat.mul_le_mul_left _ hden_le
                _ = 2 ^ (r + 2) * T r := Nat.mul_comm _ _
                _ ≤ T (r + 2) := hspan
                _ ≤ n := hn
            have hq_cut_lower : 2 ^ (r - 1) * T r ≤ n / a n := by
              apply (Nat.le_div_iff_mul_le hden_pos).2
              calc
                (2 ^ (r - 1) * T r) * a n ≤
                    (2 ^ (r - 1) * T r) * 2 ^ (r + 2) :=
                  Nat.mul_le_mul_left _ hden_le
                _ ≤ T (r + 2) := hcutspan
                _ ≤ n := hn
            have hq_value : a (n / a n) = 2 ^ r ∨ a (n / a n) = 2 ^ (r + 1) := by
              by_cases hq_mid : n / a n < T (r + 1)
              · have hq_mem := hr.2 (n / a n) hq_lower hq_mid
                rcases hq_mem.1 with hlow | hupp
                · by_cases hrzero : r = 0
                  · subst r
                    simp at hlow
                    have := a_pos (n / a n)
                    omega
                  · have hcut := hq_mem.2 hlow
                    simp only [if_neg hrzero] at hlow hcut
                    omega
                · exact Or.inl hupp
              · have hq_mid' : T (r + 1) ≤ n / a n := Nat.le_of_not_gt hq_mid
                have hq_mem := hr1.2 (n / a n) hq_mid' hq_upper
                simpa only [if_neg (show r + 1 ≠ 0 by omega), Nat.add_sub_cancel] using hq_mem.1
            have hnext_value : a (n + 1) = 2 ^ (r + 1) ∨ a (n + 1) = 2 ^ (r + 2) := by
              rw [a_step (n + 1) (by
                have := T_pos (r + 2)
                omega)]
              simp only [Nat.add_sub_cancel]
              rcases hq_value with h | h
              · left
                simp [h, pow_succ, Nat.mul_comm]
              · right
                simp [h, pow_succ, Nat.mul_comm]
            refine ⟨hnext_value, ?_⟩
            intro hnext_low
            have hq_low : a (n / a n) = 2 ^ r := by
              rw [a_step (n + 1) (by
                have := T_pos (r + 2)
                omega)] at hnext_low
              simp only [Nat.add_sub_cancel] at hnext_low
              rcases hq_value with h | h
              · exact h
              · simp only [h, pow_succ] at hnext_low
                nlinarith [show 0 < 2 ^ r by positivity]
            have hq_cut : n / a n < 2 ^ r * T (r + 1) := by
              by_cases hq_mid : n / a n < T (r + 1)
              · calc
                  n / a n < T (r + 1) := hq_mid
                  _ = 1 * T (r + 1) := by simp
                  _ ≤ 2 ^ r * T (r + 1) :=
                    Nat.mul_le_mul_right _ (one_le_pow₀ (by omega))
              · have hq_mem := hr1.2 (n / a n) (Nat.le_of_not_gt hq_mid) hq_upper
                exact hq_mem.2 (by
                  simp only [if_neg (show r + 1 ≠ 0 by omega), Nat.add_sub_cancel]
                  exact hq_low)
            have hn_product : n < (2 ^ r * T (r + 1)) * a n :=
              (Nat.div_lt_iff_lt_mul hden_pos).1 hq_cut
            have hproduct_cut :
                (2 ^ r * T (r + 1)) * 2 ^ (r + 2) <
                  2 ^ (r + 1) * T (r + 2) := by
              rw [show T (r + 2) = 2 ^ (r + 1) * T (r + 1) + 1 by simp [T]]
              simp only [pow_succ]
              nlinarith [show 0 < 2 ^ r by positivity]
            calc
              n + 1 ≤ (2 ^ r * T (r + 1)) * a n := hn_product
              _ ≤ (2 ^ r * T (r + 1)) * 2 ^ (r + 2) :=
                Nat.mul_le_mul_left _ hden_le
              _ < 2 ^ (r + 1) * T (r + 2) := hproduct_cut

/-- The least index carrying `2 ^ r` is the `r`-th term of A117261. -/
theorem alkan_a335901 : ∀ r : ℕ,
    a (T r) = 2 ^ r ∧
      ∀ k : ℕ, 1 ≤ k → a k = 2 ^ r → T r ≤ k := by
  have prefix_bound : ∀ r n : ℕ, 1 ≤ n → n < T (r + 1) → a n ≤ 2 ^ r := by
    intro r
    induction r with
    | zero =>
        intro n hn hn_upper
        have hn_eq : n = 1 := by
          simp [T] at hn_upper
          omega
        subst n
        simp [a]
    | succ r ih =>
        intro n hn hn_upper
        by_cases hprev : n < T (r + 1)
        · have hpow_le : 2 ^ r ≤ 2 ^ (r + 1) := by
            rw [pow_succ]
            nlinarith [show 0 < 2 ^ r by positivity]
          exact (ih n hn hprev).trans hpow_le
        · have hmem := (block_invariant (r + 1)).2 n
              (Nat.le_of_not_gt hprev) (by simpa only [Nat.add_assoc] using hn_upper)
          rcases hmem.1 with h | h
          · simp only [if_neg (show r + 1 ≠ 0 by omega), Nat.add_sub_cancel] at h
            have hpow_le : 2 ^ r ≤ 2 ^ (r + 1) := by
              simp only [pow_succ]
              nlinarith [show 0 < 2 ^ r by positivity]
            exact h.le.trans hpow_le
          · exact h.le
  intro r
  constructor
  · exact (block_invariant r).1
  · intro k hk hak
    cases r with
    | zero => simpa [T] using hk
    | succ r =>
        by_contra hnot
        have hbound := prefix_bound r k hk (Nat.lt_of_not_ge hnot)
        have hpow_lt : 2 ^ r < 2 ^ (r + 1) := by
          rw [pow_succ]
          nlinarith [show 0 < 2 ^ r by positivity]
        omega

#print axioms alkan_a335901

end D5.S1.Recurrence.Invariants.SelfReferentialDoublingFirstOccurrence

/- GID: D5/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/SelfReferentialQuotientFirstOccurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Tactic.Linarith, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: The first occurrence thresholds of Alkan's self-referential quotient recurrence. -/

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# First occurrences in a self-referential quotient recurrence

The value at index zero is a sentinel used only to totalize the recurrence;
the source sequence starts at index one.
-/

namespace D5.S1.Recurrence.Invariants.SelfReferentialQuotientFirstOccurrence

/-- Alkan's sequence A335925, totalized at index zero by the sentinel value one. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => a ((n + 1) / a (n + 1)) + 1
termination_by n => n
decreasing_by
  · omega
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)

/-- A000522 in its recurrence form. -/
def T : ℕ → ℕ
  | 0 => 1
  | r + 1 => (r + 1) * T r + 1

private theorem block_invariant (r : ℕ) :
    a (T r) = r + 1 ∧
      ∀ n, T r ≤ n → n < T (r + 1) →
        (a n = r ∨ a n = r + 1) ∧ (a n = r → n < r * T r) := by
  have a_pos (n : ℕ) : 0 < a n := by
    cases n with
    | zero => simp [a]
    | succ n =>
        cases n with
        | zero => simp [a]
        | succ n => simp [a]
  have T_pos (j : ℕ) : 0 < T j := by
    induction j with
    | zero => simp [T]
    | succ j ih => simp [T]
  have a_step (n : ℕ) (hn : 2 ≤ n) :
      a n = a ((n - 1) / a (n - 1)) + 1 := by
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
      have hprev_mem := hr1.2 ((r + 2) * T (r + 1)) (by
        nlinarith [T_pos (r + 1)]) (by simp [T])
      have hprev : a ((r + 2) * T (r + 1)) = r + 2 := by
        rcases hprev_mem.1 with hlow | hupp
        · have hcut := hprev_mem.2 hlow
          nlinarith [T_pos (r + 1)]
        · omega
      have hstart : a (T (r + 2)) = r + 3 := by
        rw [a_step (T (r + 2)) (by
          rw [show T (r + 2) = (r + 2) * T (r + 1) + 1 by simp [T]]
          exact Nat.succ_le_succ (Nat.mul_pos (by omega) (T_pos (r + 1))))]
        have hpred : T (r + 2) - 1 = (r + 2) * T (r + 1) := by simp [T]
        rw [hpred, hprev]
        have hdiv : ((r + 2) * T (r + 1)) / (r + 2) = T (r + 1) := by
          exact Nat.mul_div_right (T (r + 1)) (by omega)
        rw [hdiv, hr1.1]
      constructor
      · simpa only [Nat.add_assoc] using hstart
      · have hTexpand :
            T (r + 2) = ((r + 2) * (r + 1)) * T r + (r + 3) := by
          simp [T]
          ring
        have hspan : (r + 3) * T r ≤ T (r + 2) := by
          rw [hTexpand]
          rcases Nat.eq_zero_or_pos r with rfl | hrpos
          · simp [T]
          · have hcoef : r + 3 ≤ (r + 2) * (r + 1) := by nlinarith
            exact (Nat.mul_le_mul_right (T r) hcoef).trans (Nat.le_add_right _ _)
        have hcutspan : (r * T r) * (r + 3) ≤ T (r + 2) := by
          rw [hTexpand]
          have hcoef : r * (r + 3) ≤ (r + 2) * (r + 1) := by nlinarith
          calc
            (r * T r) * (r + 3) = (r * (r + 3)) * T r := by ring
            _ ≤ ((r + 2) * (r + 1)) * T r := Nat.mul_le_mul_right _ hcoef
            _ ≤ ((r + 2) * (r + 1)) * T r + (r + 3) := Nat.le_add_right _ _
        intro n hn
        induction n, hn using Nat.le_induction with
        | base =>
            intro _
            exact ⟨Or.inr hstart, by intro h; omega⟩
        | succ n hn ih =>
            intro hnext_upper
            have hn_upper : n < T (r + 2 + 1) := by omega
            have hn_mem := ih hn_upper
            have hden_pos : 0 < a n := a_pos n
            have hden_le : a n ≤ r + 3 := by rcases hn_mem.1 with h | h <;> omega
            have hq_upper : n / a n < T (r + 2) := by
              rcases hn_mem.1 with hlow | hupp
              · rw [hlow]
                apply (Nat.div_lt_iff_lt_mul (by omega)).2
                simpa [Nat.mul_comm] using hn_mem.2 hlow
              · rw [hupp]
                apply (Nat.div_lt_iff_lt_mul (by omega)).2
                have hn_bound : n < (r + 3) * T (r + 2) := by
                  rw [show T (r + 2 + 1) = (r + 3) * T (r + 2) + 1 by simp [T]] at hnext_upper
                  omega
                simpa [Nat.mul_comm] using hn_bound
            have hq_lower : T r ≤ n / a n := by
              apply (Nat.le_div_iff_mul_le hden_pos).2
              calc
                T r * a n ≤ T r * (r + 3) := Nat.mul_le_mul_left _ hden_le
                _ = (r + 3) * T r := Nat.mul_comm _ _
                _ ≤ T (r + 2) := hspan
                _ ≤ n := hn
            have hq_cut_lower : r * T r ≤ n / a n := by
              apply (Nat.le_div_iff_mul_le hden_pos).2
              calc
                (r * T r) * a n ≤ (r * T r) * (r + 3) :=
                  Nat.mul_le_mul_left _ hden_le
                _ ≤ T (r + 2) := hcutspan
                _ ≤ n := hn
            have hq_value : a (n / a n) = r + 1 ∨ a (n / a n) = r + 2 := by
              by_cases hq_mid : n / a n < T (r + 1)
              · have hq_mem := hr.2 (n / a n) hq_lower hq_mid
                rcases hq_mem.1 with hlow | hupp
                · have hcut := hq_mem.2 hlow
                  omega
                · exact Or.inl hupp
              · have hq_mid' : T (r + 1) ≤ n / a n := Nat.le_of_not_gt hq_mid
                exact hr1.2 (n / a n) hq_mid' hq_upper |>.1
            have hnext_value : a (n + 1) = r + 2 ∨ a (n + 1) = r + 3 := by
              rw [a_step (n + 1) (by
                have := T_pos (r + 2)
                omega)]
              simp only [Nat.add_sub_cancel]
              rcases hq_value with h | h <;> omega
            refine ⟨hnext_value, ?_⟩
            intro hnext_low
            have hq_low : a (n / a n) = r + 1 := by
              rw [a_step (n + 1) (by
                have := T_pos (r + 2)
                omega)] at hnext_low
              simp only [Nat.add_sub_cancel] at hnext_low
              rcases hq_value with h | h <;> omega
            have hq_cut : n / a n < (r + 1) * T (r + 1) := by
              by_cases hq_mid : n / a n < T (r + 1)
              · calc
                  n / a n < T (r + 1) := hq_mid
                  _ = 1 * T (r + 1) := by simp
                  _ ≤ (r + 1) * T (r + 1) :=
                    Nat.mul_le_mul_right _ (by omega)
              · exact hr1.2 (n / a n) (Nat.le_of_not_gt hq_mid) hq_upper |>.2 hq_low
            have hn_product : n < ((r + 1) * T (r + 1)) * a n :=
              (Nat.div_lt_iff_lt_mul hden_pos).1 hq_cut
            have hproduct_cut :
                ((r + 1) * T (r + 1)) * (r + 3) < (r + 2) * T (r + 2) := by
              rw [show T (r + 2) = (r + 2) * T (r + 1) + 1 by simp [T]]
              nlinarith [T_pos (r + 1)]
            calc
              n + 1 ≤ ((r + 1) * T (r + 1)) * a n := hn_product
              _ ≤ ((r + 1) * T (r + 1)) * (r + 3) :=
                Nat.mul_le_mul_left _ hden_le
              _ < (r + 2) * T (r + 2) := hproduct_cut

/-- For every positive value `m`, the first index carrying `m` is the
`(m - 1)`-st term of A000522. -/
theorem alkan_a335925 : ∀ m : ℕ, 1 ≤ m →
    a (T (m - 1)) = m ∧
      ∀ k : ℕ, 1 ≤ k → a k = m → T (m - 1) ≤ k := by
  have prefix_bound : ∀ r n : ℕ, 1 ≤ n → n < T (r + 1) → a n ≤ r + 1 := by
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
        · exact (ih n hn hprev).trans (by omega)
        · have hmem := (block_invariant (r + 1)).2 n
            (Nat.le_of_not_gt hprev) (by simpa only [Nat.add_assoc] using hn_upper)
          rcases hmem.1 with h | h <;> omega
  intro m hm
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hm
  constructor
  · have hind : 1 + p - 1 = p := by omega
    rw [hind]
    simpa [Nat.add_comm] using (block_invariant p).1
  · intro k hk hak
    cases p with
    | zero => simpa [T] using hk
    | succ p =>
        have hind : 1 + (p + 1) - 1 = p + 1 := by omega
        rw [hind]
        by_contra hnot
        have hbound := prefix_bound p k hk (Nat.lt_of_not_ge hnot)
        omega

#print axioms alkan_a335925

end D5.S1.Recurrence.Invariants.SelfReferentialQuotientFirstOccurrence

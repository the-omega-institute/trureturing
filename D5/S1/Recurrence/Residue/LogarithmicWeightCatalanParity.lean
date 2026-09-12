/- GID: D5/S1/Recurrence/Residue/LogarithmicWeightCatalanParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Residue/LogarithmicWeightCatalanParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Integer triangular construction and ternary alternation for OEIS A397349. -/
import Mathlib
/- The two integer sequences in this module are not identified with the
   Catalan sequence: only the proposed parity property is compared with it. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S1.Recurrence.Residue.LogarithmicWeightCatalanParity
noncomputable def s : ℕ → ℤ := fun n => Nat.strongRecOn n (fun n rec =>
  if n ≤ 1 then 0 else
    Finset.sum (Finset.range (n - 1)) (fun j =>
      (if _h : j + 1 < n then
        (if j + 1 = 1 then 1 else (3 * (j + 1 : ℤ)^2 - 1) * rec (j + 1) (by omega)) *
        (if n - (j + 1) ≤ 1 then 1 else 3 * (n - (j + 1) : ℤ) * rec (n - (j + 1)) (by omega))
       else 0))
  )
  termination_by n => n
noncomputable def a (n : ℕ) : ℤ := if n = 1 then 1 else (3 * (n : ℤ)^2 - 1) * s n
noncomputable def b (n : ℕ) : ℤ := if n ≤ 1 then 1 else 3 * (n : ℤ) * s n
theorem s_zero : s 0 = 0 := by simp [s, Nat.strongRecOn_eq]
theorem s_one : s 1 = 0 := by simp [s, Nat.strongRecOn_eq]
theorem a_one : a 1 = 1 := by simp [a]
private theorem s_eq_sum (n : ℕ) (hn : 2 ≤ n) :
    s n = ∑ j ∈ Finset.range (n - 1), a (j + 1) * b (n - (j + 1)) := by
  rw [s, Nat.strongRecOn_eq]
  simp only [if_neg (by omega : ¬n ≤ 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j + 1 < n := by simp only [Finset.mem_range] at hj; omega
  simp only [dif_pos hjn, a, b, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub (by omega : j + 1 ≤ n)]
  rfl

private theorem b_mod_three (m : ℕ) (hm : 2 ≤ m) : b m % 3 = 0 := by
  simp [b, show ¬m ≤ 1 by omega, Int.mul_emod]

private theorem s_mod_three (n : ℕ) (hn : 2 ≤ n) :
    s n % 3 = a (n - 1) % 3 := by
  rw [s_eq_sum n hn, Finset.sum_int_mod]
  rw [Finset.sum_eq_single (n - 2)]
  · have hlast : n - 2 + 1 = n - 1 := by omega
    simp [hlast, show n - (n - 1) = 1 by omega, b]
  · intro j hj hne
    have hm : 2 ≤ n - (j + 1) := by
      simp only [Finset.mem_range] at hj
      omega
    rw [Int.mul_emod, b_mod_three _ hm]
    simp
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

private theorem a_mod_three_step (n : ℕ) (hn : 2 ≤ n) :
    a n % 3 = (2 * (a (n - 1) % 3)) % 3 := by
  rw [a, if_neg (by omega : n ≠ 1), Int.mul_emod, s_mod_three n hn]
  norm_num [Int.sub_emod, Int.mul_emod]

theorem hanna_conjecture_a397349_mod_three :
    ∀ n : ℕ, 1 ≤ n → a n % 3 = if n % 2 = 1 then 1 else 2 := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    intro hn
    by_cases hzero : n = 0
    · subst n
      norm_num [a_one]
    · by_cases hone : n = 1
      · subst n
        have hs : s 2 = 1 := by
          rw [s_eq_sum 2 (by omega)]
          norm_num [a_one, b]
        norm_num [a, hs]
      have hnpos : 1 ≤ n := by omega
      rw [a_mod_three_step (n + 1) (by omega)]
      simp only [Nat.add_sub_cancel, ih hnpos]
      have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hmod with hmod | hmod
      · have hnext : (n + 1) % 2 = 1 := by omega
        norm_num [hmod, hnext]
      · have hnext : (n + 1) % 2 = 0 := by omega
        norm_num [hmod, hnext]

#print axioms hanna_conjecture_a397349_mod_three
def parity_conjecture : Prop := ∀ n : ℕ, Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k
end D5.S1.Recurrence.Residue.LogarithmicWeightCatalanParity

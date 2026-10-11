/- GID: D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CycleSums/ConsecutiveCycleSumsArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interval subset sums and minimal triangular cores bound consecutive cycle completion. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsArithmetic

open Finset

/-- The total of labels one through n. -/
def tri (n : ℕ) : ℕ := n * (n + 1) / 2

private theorem tri_succ (n : ℕ) : tri (n + 1) = tri n + (n + 1) := by
  have h := Nat.triangle_succ (n + 1)
  simpa [tri, Nat.mul_comm] using h

private theorem tri_eq_sum (n : ℕ) : tri n = ∑ i ∈ range n, (i + 1) := by
  have h := Finset.sum_range_id (n + 1)
  rw [Finset.sum_range_succ'] at h
  simpa [tri, Nat.mul_comm] using h.symm

private theorem tri_double (n : ℕ) : 2 * tri n = n * (n + 1) := by
  have h := Finset.sum_range_id_mul_two (n + 1)
  have hs : (∑ i ∈ range (n + 1), i) = ∑ i ∈ range n, (i + 1) := by
    rw [Finset.sum_range_succ']
    simp
  rw [hs, ← tri_eq_sum] at h
  simpa [Nat.mul_comm] using h

private theorem tri_overlap {k : ℕ} (hk : 4 ≤ k) : k + 5 ≤ tri k := by
  have h := tri_double k
  have hprod : 0 ≤ (k - 4) * (k - 1) := Nat.zero_le _
  have hsub : k - 4 + 4 = k := by omega
  have hsub1 : k - 1 + 1 = k := by omega
  nlinarith

/-- All sums between two and three less than the triangular total occur in the core. -/
theorem subset_sums {k s : ℕ} (hk : 4 ≤ k) (hs : 2 ≤ s) (ht : s + 3 ≤ tri k) :
    ∃ S : Finset ℕ, (∀ x ∈ S, 2 ≤ x ∧ x ≤ k) ∧ ∑ x ∈ S, x = s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d generalizing s with
  | zero =>
      norm_num [tri] at ht
      have hsupper : s ≤ 7 := by omega
      interval_cases s
      · exact ⟨{2}, by simp, by simp⟩
      · exact ⟨{3}, by simp, by simp⟩
      · exact ⟨{4}, by simp, by simp⟩
      · exact ⟨{2, 3}, by simp_all, by simp⟩
      · exact ⟨{2, 4}, by simp_all, by simp⟩
      · exact ⟨{3, 4}, by simp_all, by simp⟩
  | succ d ih =>
      let k := 4 + d
      have hk : 4 ≤ k := by dsimp [k]; omega
      change s + 3 ≤ tri (k + 1) at ht
      by_cases hlo : s + 3 ≤ tri k
      · obtain ⟨S, hS, hsum⟩ := ih hs hk hlo
        refine ⟨S, ?_, hsum⟩
        intro x hx
        have h := hS x hx
        exact ⟨h.1, by omega⟩
      · have hover := tri_overlap hk
        have hslarge : k + 3 ≤ s := by omega
        have hsrem : 2 ≤ s - (k + 1) := by omega
        have htrem : s - (k + 1) + 3 ≤ tri k := by rw [tri_succ] at ht; omega
        obtain ⟨S, hS, hsum⟩ := ih hsrem hk htrem
        have hnot : k + 1 ∉ S := by intro hm; have := (hS _ hm).2; omega
        refine ⟨insert (k + 1) S, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · constructor <;> omega
          · have h := hS x hx
            exact ⟨h.1, by omega⟩
        · rw [sum_insert hnot, hsum]
          omega

/-- The least usable core is strictly shorter than the cycle and has a square-root budget. -/
theorem choose_core {n : ℕ} (hn : 8 ≤ n) :
    ∃ k : ℕ, 4 ≤ k ∧ k < n ∧ n + 4 ≤ tri k ∧ (k - 1) ^ 2 < 2 * n + 8 := by
  have hex : ∃ k : ℕ, 4 ≤ k ∧ n + 4 ≤ tri k := by
    refine ⟨n - 1, by omega, ?_⟩
    have h := tri_double (n - 1)
    have heq : n - 1 + 1 = n := by omega
    rw [heq] at h
    have hpos : 0 ≤ (n - 8) * (n - 1) := Nat.zero_le _
    have hsub : n - 8 + 8 = n := by omega
    have hsub1 : n - 1 + 1 = n := by omega
    nlinarith
  let k := Nat.find hex
  have hk : 4 ≤ k ∧ n + 4 ≤ tri k := Nat.find_spec hex
  have hkn : k ≤ n - 1 := Nat.find_min' hex (by
    constructor
    · omega
    · have h := tri_double (n - 1)
      have hsub : n - 1 + 1 = n := by omega
      have hsub8 : n - 8 + 8 = n := by omega
      rw [hsub] at h
      have hpos := Nat.zero_le ((n - 8) * (n - 1))
      nlinarith)
  have hk5 : 5 ≤ k := by
    by_contra hbad
    have heq : k = 4 := by omega
    have hh := hk.2
    rw [heq] at hh
    norm_num [tri] at hh
    omega
  have hmin : tri (k - 1) < n + 4 := by
    have hm := Nat.find_min hex (show k - 1 < k by omega)
    have hkl : 4 ≤ k - 1 := by omega
    change ¬ (4 ≤ k - 1 ∧ n + 4 ≤ tri (k - 1)) at hm
    omega
  refine ⟨k, hk.1, by omega, hk.2, ?_⟩
  have hdouble := tri_double (k - 1)
  have hsub : k - 1 + 1 = k := by omega
  rw [hsub] at hdouble
  have hsmall : (k - 1) ^ 2 < (k - 1) * k := by nlinarith
  nlinarith

/-- The consecutive tail labels after the core, up to endpoint j. -/
def tail (k j : ℕ) : ℕ := ∑ x ∈ Finset.Icc (k + 1) j, x

private theorem tail_self (k : ℕ) : tail k k = 0 := by
  simp [tail]

private theorem tail_succ {k j : ℕ} (hj : k ≤ j) :
    tail k (j + 1) = tail k j + (j + 1) := by
  exact Finset.sum_Icc_succ_top (by omega) (fun x : ℕ => x)

private theorem tri_tail {k j : ℕ} (hj : k ≤ j) : tri j = tri k + tail k j := by
  have h := Finset.sum_range_add_sum_Ico (fun x : ℕ => x)
    (Nat.add_le_add_right hj 1)
  have htot (m : ℕ) : (∑ x ∈ Finset.range (m + 1), x) = tri m := by
    simpa [tri, Nat.mul_comm] using Finset.sum_range_id (m + 1)
  rw [htot, htot, Finset.Ico_add_one_right_eq_Icc] at h
  exact h.symm

/-- Tail translates of the core interval cover every interior target sum. -/
theorem interval_cover {n k q : ℕ} (hkn : k ≤ n) (htri : n + 4 ≤ tri k)
    (hq : 3 ≤ q) (hupper : q + 2 ≤ tri n) :
    ∃ j : ℕ, k ≤ j ∧ j ≤ n ∧ 3 + tail k j ≤ q ∧ q + 2 ≤ tri k + tail k j := by
  have hcover : ∀ m : ℕ, k ≤ m → m + 4 ≤ tri k → ∀ s : ℕ,
      3 ≤ s → s + 2 ≤ tri m →
      ∃ j : ℕ, k ≤ j ∧ j ≤ m ∧ 3 + tail k j ≤ s ∧ s + 2 ≤ tri k + tail k j := by
    intro m hkm
    induction m, hkm using Nat.le_induction with
    | base =>
        intro _ s hs hu
        refine ⟨k, le_rfl, le_rfl, ?_, ?_⟩
        · simpa [tail_self] using hs
        · simpa [tail_self] using hu
    | succ m hkm ih =>
        intro ht s hs hu
        by_cases hold : s + 2 ≤ tri m
        · obtain ⟨j, hkj, hjm, hjlo, hjhi⟩ := ih (by omega) s hs hold
          exact ⟨j, hkj, by omega, hjlo, hjhi⟩
        · refine ⟨m + 1, by omega, le_rfl, ?_, ?_⟩
          · have hm := tri_tail hkm
            have hnext := tail_succ hkm
            omega
          · rw [tri_tail (show k ≤ m + 1 by omega)] at hu
            exact hu
  exact hcover n hkn htri q hq hupper

theorem sum_Icc_one (n : ℕ) : (∑ x ∈ Finset.Icc 1 n, x) = tri n := by
  have h := tri_tail (Nat.zero_le n)
  simpa [tri, tail] using h.symm

theorem sum_Icc_two {n : ℕ} (hn : 1 ≤ n) :
    (∑ x ∈ Finset.Icc 2 n, x) = tri n - 1 := by
  have h := tri_tail hn
  change tri n = tri 1 + ∑ x ∈ Finset.Icc 2 n, x at h
  norm_num [tri] at h ⊢
  omega

end D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsArithmetic

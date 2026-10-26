/- GID: D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight
   mirror-E: none(waiver:general-partition-estimate)
   anchors: []
   utility: none
   digest: Sharp maxima and factorial absorption for multiplicity-weighted positive partitions. -/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Sharp multiplicity weights of positive integer partitions and factorial absorption. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight

/-- The multiplicity weight, including the factorial of the number of parts equal to one. -/
def weight (p : Multiset ℕ) : ℕ :=
  ∏ l ∈ p.toFinset, (l * (2 ^ l - 1)) ^ p.count l * (p.count l).factorial

/-- The largest multiplicity weight of a positive partition of n. -/
def maximumWeight (n : ℕ) : ℕ :=
  (Finset.univ : Finset (Nat.Partition n)).sup (fun p => weight p.parts)

private def envelope : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 6
  | 3 => 21
  | 4 => 72
  | 5 => 155
  | 6 => 1296
  | n + 7 => (n + 7).factorial

private theorem envelope_large {n : ℕ} (hn : 7 ≤ n) : envelope n = n.factorial := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hk
  subst n
  rfl

private theorem factorial_le_envelope (n : ℕ) : n.factorial ≤ envelope n := by
  by_cases h : 7 ≤ n
  · rw [envelope_large h]
  · have hn : n ≤ 6 := by omega
    interval_cases n <;> norm_num [envelope]

private theorem envelope_mul_large {a : ℕ} (ha : 7 ≤ a) (b : ℕ) :
    envelope a * envelope b ≤ envelope (a + b) := by
  rw [envelope_large ha, envelope_large (by omega : 7 ≤ a + b)]
  by_cases hb : 7 ≤ b
  · rw [envelope_large hb]
    exact Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add a b)
  · have hbsmall : b ≤ 6 := by omega
    have hsmall : envelope b ≤ (8 : ℕ).ascFactorial b := by
      interval_cases b <;> norm_num [envelope, Nat.ascFactorial]
    calc
      a.factorial * envelope b ≤ a.factorial * (a + 1).ascFactorial b :=
        Nat.mul_le_mul_left _ (hsmall.trans (Nat.ascFactorial_le b (by omega)))
      _ = (a + b).factorial := Nat.factorial_mul_ascFactorial a b

private theorem envelope_mul (a b : ℕ) : envelope a * envelope b ≤ envelope (a + b) := by
  by_cases ha : 7 ≤ a
  · exact envelope_mul_large ha b
  by_cases hb : 7 ≤ b
  · simpa [Nat.mul_comm, Nat.add_comm] using envelope_mul_large hb a
  have ha6 : a ≤ 6 := by omega
  have hb6 : b ≤ 6 := by omega
  interval_cases a <;> interval_cases b <;> norm_num [envelope]

private theorem factor_le_factorial {l : ℕ} (hl : 6 ≤ l) :
    l * (2 ^ l - 1) ≤ l.factorial := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ l hl ih =>
      have hp : 2 ≤ 2 ^ l := by
        calc
          2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ l := by gcongr; omega
      have hs : 2 ^ l - 1 + 1 = 2 ^ l := Nat.sub_add_cancel (by omega)
      have hp2 : 0 < 2 ^ (l + 1) := by positivity
      have hs2 : 2 ^ (l + 1) - 1 + 1 = 2 ^ (l + 1) :=
        Nat.sub_add_cancel (by omega)
      have hc : 2 ^ (l + 1) - 1 ≤ l * (2 ^ l - 1) := by
        rw [pow_succ] at hs2
        have hmul := Nat.mul_le_mul_right (2 ^ l - 1) hl
        rw [pow_succ]
        nlinarith
      calc
        (l + 1) * (2 ^ (l + 1) - 1) ≤ (l + 1) * (l * (2 ^ l - 1)) := Nat.mul_le_mul_left _ hc
        _ ≤ (l + 1) * l.factorial := Nat.mul_le_mul_left _ ih
        _ = (l + 1).factorial := (Nat.factorial_succ l).symm

private theorem homogeneous_large {l : ℕ} (hl : 6 ≤ l) (m : ℕ) :
    (l * (2 ^ l - 1)) ^ m * m.factorial ≤ (l * m).factorial := by
  have he := Nat.uniformBell_mul_eq m (by omega : l ≠ 0)
  have hb : 1 ≤ Nat.uniformBell m l := by
    by_contra h
    have hz : Nat.uniformBell m l = 0 := by omega
    exact Nat.factorial_ne_zero (m * l) (by simpa [hz] using he.symm)
  calc
    (l * (2 ^ l - 1)) ^ m * m.factorial ≤ l.factorial ^ m * m.factorial :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (factor_le_factorial hl) m)
    _ = 1 * l.factorial ^ m * m.factorial := by simp
    _ ≤ Nat.uniformBell m l * l.factorial ^ m * m.factorial :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb)
    _ = (l * m).factorial := by simpa [Nat.mul_comm] using he

private theorem homogeneous_step {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m)
    (hc : l * (2 ^ l - 1) ≤ l.factorial * (2 * l - 1).choose (l - 1))
    (ih : (l * (2 ^ l - 1)) ^ m * m.factorial ≤ (l * m).factorial) :
    (l * (2 ^ l - 1)) ^ (m + 1) * (m + 1).factorial ≤ (l * (m + 1)).factorial := by
  have htop : 2 * l - 1 ≤ m * l + l - 1 := by
    have hmul := Nat.mul_le_mul_right l hm
    omega
  have hc' : l * (2 ^ l - 1) ≤ l.factorial * (m * l + l - 1).choose (l - 1) :=
    hc.trans (Nat.mul_le_mul_left _ (Nat.choose_le_choose (l - 1) htop))
  have he := Nat.add_choose_mul_factorial_mul_factorial (m * l) l
  rw [Nat.choose_mul_add (by omega : l ≠ 0)] at he
  calc
    (l * (2 ^ l - 1)) ^ (m + 1) * (m + 1).factorial =
        ((l * (2 ^ l - 1)) ^ m * m.factorial) * (l * (2 ^ l - 1)) * (m + 1) := by
          rw [pow_succ, Nat.factorial_succ]; ring
    _ ≤ (l * m).factorial * (l.factorial * (m * l + l - 1).choose (l - 1)) * (m + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul ih hc')
    _ = (l * (m + 1)).factorial := by
      simpa only [Nat.mul_add, Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using he

private theorem homogeneous_small {l m : ℕ} (hl : 2 ≤ l) (hl' : l ≤ 5)
    (hm : 7 ≤ l * m) :
    (l * (2 ^ l - 1)) ^ m * m.factorial ≤ (l * m).factorial := by
  have step : ∀ k : ℕ, 1 ≤ k →
      (l * (2 ^ l - 1)) ^ k * k.factorial ≤ (l * k).factorial →
      (l * (2 ^ l - 1)) ^ (k + 1) * (k + 1).factorial ≤ (l * (k + 1)).factorial := by
    intro k hk hi
    apply homogeneous_step (by omega) hk _ hi
    interval_cases l <;> norm_num [Nat.choose]
  interval_cases l
  · have h : 4 ≤ m := by omega
    induction m, h using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => exact step k (by omega) (ih (by omega))
  · have h : 3 ≤ m := by omega
    induction m, h using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => exact step k (by omega) (ih (by omega))
  · have h : 2 ≤ m := by omega
    induction m, h using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => exact step k (by omega) (ih (by omega))
  · have h : 2 ≤ m := by omega
    induction m, h using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => exact step k (by omega) (ih (by omega))

private theorem homogeneous_envelope {l m : ℕ} (hl : 1 ≤ l) (hm : 1 ≤ m) :
    (l * (2 ^ l - 1)) ^ m * m.factorial ≤ envelope (l * m) := by
  by_cases hl1 : l = 1
  · subst l
    simpa using factorial_le_envelope m
  by_cases hl6 : 6 ≤ l
  · exact (homogeneous_large hl6 m).trans (factorial_le_envelope _)
  by_cases hlarge : 7 ≤ l * m
  · exact (homogeneous_small (by omega) (by omega) hlarge).trans (factorial_le_envelope _)
  have hl' : l ≤ 5 := by omega
  have hm' : m ≤ 6 := by
    have hmul := Nat.mul_le_mul_right m hl
    omega
  interval_cases l <;> interval_cases m <;> norm_num [envelope] at *

private theorem weight_le_envelope (p : Multiset ℕ) (hp : ∀ l ∈ p, 0 < l) :
    weight p ≤ envelope p.sum := by
  have h : ∀ T : Finset ℕ, T ⊆ p.toFinset →
      (∏ l ∈ T, (l * (2 ^ l - 1)) ^ p.count l * (p.count l).factorial) ≤
        envelope (∑ l ∈ T, l * p.count l) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [envelope]
    | @insert l T hl ih =>
      intro hT
      have hlp : l ∈ p := Multiset.mem_toFinset.mp (hT (Finset.mem_insert_self _ _))
      have hcount : 1 ≤ p.count l := Multiset.count_pos.mpr hlp
      rw [Finset.prod_insert hl, Finset.sum_insert hl]
      exact (Nat.mul_le_mul (homogeneous_envelope (hp l hlp) hcount)
        (ih (Finset.Subset.trans (Finset.subset_insert _ _) hT))).trans
          (envelope_mul _ _)
  have he := h p.toFinset (Finset.Subset.refl _)
  have hs : p.sum = ∑ l ∈ p.toFinset, l * p.count l := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using Finset.sum_multiset_count p
  simpa only [weight, ← hs] using he

private theorem maximumWeight_le_envelope (n : ℕ) : maximumWeight n ≤ envelope n := by
  change (Finset.univ : Finset (Nat.Partition n)).sup (fun p => weight p.parts) ≤ envelope n
  obtain ⟨p, _, he⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Nat.Partition n)) Finset.univ_nonempty (fun p => weight p.parts)
  rw [he]
  simpa [p.parts_sum] using weight_le_envelope p.parts (fun _ h => p.parts_pos h)

private theorem ones_lower (n : ℕ) : n.factorial ≤ maximumWeight n := by
  let p : Nat.Partition n :=
    ⟨Multiset.replicate n 1, by
      intro i hi
      have hi1 := (Multiset.mem_replicate.mp hi).2
      omega, by simp⟩
  have hw : weight p.parts = n.factorial := by
    by_cases hn : n = 0
    · subst n; simp [p, weight]
    · simp [p, weight, Multiset.toFinset_replicate, hn]
  rw [← hw]
  exact Finset.le_sup (f := fun q : Nat.Partition n => weight q.parts) (Finset.mem_univ p)

private theorem maximumWeight_eq_envelope (n : ℕ) : maximumWeight n = envelope n := by
  apply Nat.le_antisymm (maximumWeight_le_envelope n)
  by_cases hn : 7 ≤ n
  · rw [envelope_large hn]
    exact ones_lower n
  have witness (k : ℕ) (p : Nat.Partition k) : weight p.parts ≤ maximumWeight k :=
    Finset.le_sup (f := fun q : Nat.Partition k => weight q.parts) (Finset.mem_univ p)
  have hn6 : n ≤ 6 := by omega
  interval_cases n
  · simpa [envelope] using ones_lower 0
  · simpa [envelope] using ones_lower 1
  · let p : Nat.Partition 2 := ⟨{2}, by simp, by norm_num⟩
    simpa [p, weight, envelope] using witness 2 p
  · let p : Nat.Partition 3 := ⟨{3}, by simp, by norm_num⟩
    simpa [p, weight, envelope] using witness 3 p
  · let p : Nat.Partition 4 := ⟨{2, 2}, by simp, by norm_num⟩
    simpa [p, weight, envelope] using witness 4 p
  · let p : Nat.Partition 5 := ⟨{5}, by simp, by norm_num⟩
    simpa [p, weight, envelope] using witness 5 p
  · let p : Nat.Partition 6 := ⟨{2, 2, 2}, by simp, by norm_num⟩
    simpa [p, weight, envelope, Nat.factorial] using witness 6 p

/-- In dimension at least seven every positive partition has weight at most the factorial. -/
theorem weight_le_factorial {n : ℕ} (hn : 7 ≤ n) (p : Nat.Partition n) :
    weight p.parts ≤ n.factorial := by
  simpa [p.parts_sum, envelope_large hn] using
    weight_le_envelope p.parts (fun _ h => p.parts_pos h)

/-- The six exceptional sharp maxima. -/
theorem maximum_weight_small :
    maximumWeight 1 = 1 ∧ maximumWeight 2 = 6 ∧ maximumWeight 3 = 21 ∧
    maximumWeight 4 = 72 ∧ maximumWeight 5 = 155 ∧ maximumWeight 6 = 1296 := by
  simp only [maximumWeight_eq_envelope]
  norm_num [envelope]

/-- The all-ones partition attains the factorial maximum in every dimension at least seven. -/
theorem maximum_weight_eq_factorial {n : ℕ} (hn : 7 ≤ n) :
    maximumWeight n = n.factorial := by
  rw [maximumWeight_eq_envelope, envelope_large hn]

private theorem envelope_absorption {s n : ℕ} (hs : 1 ≤ s) (hsn : s ≤ n) :
    envelope s * (n - s + 1).factorial ≤ envelope n := by
  by_cases heq : s = n
  · subst s; simp
  by_cases hs1 : s = 1
  · subst s
    have hsub : n - 1 + 1 = n := by omega
    simpa [envelope, hsub] using factorial_le_envelope n
  by_cases hn : n ≤ 6
  · have hs6 : s ≤ 6 := hsn.trans hn
    interval_cases n <;> interval_cases s <;> norm_num [envelope] at *
  have hn7 : 7 ≤ n := by omega
  rw [envelope_large hn7]
  have hlen : s - 1 ≤ n := by omega
  have hsub : n - (s - 1) = n - s + 1 := by omega
  suffices h : envelope s ≤ n.descFactorial (s - 1) by
    calc
      envelope s * (n - s + 1).factorial ≤
          n.descFactorial (s - 1) * (n - s + 1).factorial := Nat.mul_le_mul_right _ h
      _ = n.factorial := by
        rw [Nat.mul_comm, ← hsub]
        exact Nat.factorial_mul_descFactorial hlen
  by_cases hs6 : s ≤ 6
  · have hbase : envelope s ≤ (7 : ℕ).descFactorial (s - 1) := by
      interval_cases s <;> norm_num [envelope, Nat.descFactorial] at *
    exact hbase.trans (Nat.descFactorial_le (s - 1) hn7)
  have hs7 : 7 ≤ s := by omega
  rw [envelope_large hs7]
  have he := Nat.factorial_mul_descFactorial (show s - 1 ≤ s + 1 by omega)
  rw [show s + 1 - (s - 1) = 2 by omega] at he
  norm_num only [show Nat.factorial 2 = 2 from rfl] at he
  rw [Nat.factorial_succ s] at he
  have hb : s.factorial ≤ (s + 1).descFactorial (s - 1) := by
    have hmul := Nat.mul_le_mul_right s.factorial (show 2 ≤ s + 1 by omega)
    nlinarith
  exact hb.trans (Nat.descFactorial_le (s - 1) (by omega))

/-- Sharp maxima absorb the factorial of the remaining dimension, with the required shift by one. -/
theorem maximum_weight_mul_factorial_le {s n : ℕ} (hs : 1 ≤ s) (hsn : s ≤ n) :
    maximumWeight s * (n - s + 1).factorial ≤ maximumWeight n := by
  rw [maximumWeight_eq_envelope, maximumWeight_eq_envelope]
  exact envelope_absorption hs hsn

end D5.S3.Combinatorics.Partitions.EvolutionAutomorphismWeight

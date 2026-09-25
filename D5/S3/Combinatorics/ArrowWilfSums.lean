/- GID: D5/S3/Combinatorics/ArrowWilfSums
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfSums
   mirror-E: none(waiver:finite-binomial-sums-for-arrow-wilf-equivalence)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: A reindexed hockey-stick identity combines the inner sums in the arrow-Wilf formulas. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Order.Interval.Finset.SuccPred
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfSums

open Nat

/-- Theorem 3.1's finite formula for the first avoidance class. -/
def F1 (n : ℕ) : ℕ :=
  numDerangements n +
    ∑ m ∈ Finset.Icc 1 n,
      ∑ k ∈ Finset.range (n - m + 1),
        (n - m).choose k * (m + k - 1).choose (n - m) * numDerangements k

/-- Theorem 5.5's finite formula for the second avoidance class. -/
def F2 (n : ℕ) : ℕ :=
  numDerangements n + numDerangements (n - 1) +
    ∑ m ∈ Finset.Icc 1 (n - 1),
      ∑ r ∈ Finset.range m,
        (m - 1).choose r * (n - m + r - 1).choose r *
          r.factorial * numDerangements (m - 1 - r)

/-- The reindexed hockey-stick identity used in equation (4.12). -/
theorem reversed_hockey_stick (n i t : ℕ) (hit : i ≤ t) (htn : t + 2 ≤ n) :
    ∑ k ∈ Finset.Icc i t, (n - k - 2).choose (t - k) =
      (n - i - 1).choose (t - i) := by
  induction hit using Nat.decreasingInduction with
  | self =>
      simp
  | of_succ i hi ih =>
      have hnot : i ∉ Finset.Icc (i + 1) t := by simp
      rw [← Finset.insert_Icc_succ_left_eq_Icc (Nat.le_of_lt hi),
        show Order.succ i = i + 1 by rfl, Finset.sum_insert hnot, ih]
      have hni : n - i - 1 = (n - i - 2) + 1 := by omega
      have hti : t - i = (t - (i + 1)) + 1 := by omega
      have hni' : n - (i + 1) - 1 = n - i - 2 := by omega
      rw [hni, hti, Nat.choose_succ_succ']
      rw [hni']
      exact Nat.add_comm _ _

/-- Swapping the triangular sums and applying the reindexed hockey-stick identity. -/
theorem weighted_hockey_transform {R : Type*} [CommSemiring R]
    (n t : ℕ) (htn : t + 2 ≤ n) (a : ℕ → R) :
    ∑ k ∈ Finset.range (t + 1),
      ((n - k - 2).choose (t - k) : R) * ∑ i ∈ Finset.range (k + 1), a i =
    ∑ i ∈ Finset.range (t + 1), ((n - i - 1).choose (t - i) : R) * a i := by
  let S := Finset.range (t + 1)
  have htriangle (k : ℕ) (hk : k ∈ S) :
      ∑ i ∈ Finset.range (k + 1), ((n - k - 2).choose (t - k) : R) * a i =
      ∑ i ∈ S, if i ≤ k then ((n - k - 2).choose (t - k) : R) * a i else 0 := by
    have hfilter : S.filter (fun i => i ≤ k) = Finset.range (k + 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, S]
      have hkt : k ≤ t := Finset.mem_range_succ_iff.mp hk
      omega
    rw [← hfilter, Finset.sum_filter]
  calc
    _ = ∑ k ∈ S, ∑ i ∈ S,
        if i ≤ k then ((n - k - 2).choose (t - k) : R) * a i else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          exact htriangle k hk
    _ = ∑ i ∈ S, ∑ k ∈ S,
        if i ≤ k then ((n - k - 2).choose (t - k) : R) * a i else 0 :=
          Finset.sum_comm
    _ = ∑ i ∈ S, ((n - i - 1).choose (t - i) : R) * a i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hit : i ≤ t := Finset.mem_range_succ_iff.mp hi
          have hfilter : S.filter (fun k => i ≤ k) = Finset.Icc i t := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, S]
            omega
          rw [← Finset.sum_filter, hfilter]
          simp_rw [← Finset.sum_mul]
          have hh :
              (∑ k ∈ Finset.Icc i t, ((n - k - 2).choose (t - k) : R)) =
                ((n - i - 1).choose (t - i) : R) := by
            simpa only [Nat.cast_sum] using
              congrArg (fun x : ℕ => (x : R)) (reversed_hockey_stick n i t hit htn)
          rw [hh]

/-- The signed finite sum appearing as the coefficient in equation (4.5). -/
def E (n : ℕ) : ℤ :=
  ∑ t ∈ Finset.range n,
    ∑ i ∈ Finset.range (t + 1),
      (-1 : ℤ) ^ i * (Nat.ascFactorial (i + 1) (t - i) : ℤ) *
        ((n - i - 1).choose (t - i) : ℤ)

/-- Reindex the second formula's correction by `t = m - 1` and `k = t - r`. -/
theorem f2_correction_reindexed (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 (n - 1),
      ∑ r ∈ Finset.range m,
        (m - 1).choose r * (n - m + r - 1).choose r *
          r.factorial * numDerangements (m - 1 - r)) =
    ∑ t ∈ Finset.range (n - 1),
      ∑ k ∈ Finset.range (t + 1),
        t.choose (t - k) * (n - k - 2).choose (t - k) *
          (t - k).factorial * numDerangements k := by
  have hIcc : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro t ht
  have htn : t + 2 ≤ n := by
    have := Finset.mem_range.mp ht
    omega
  simp only [Nat.add_comm 1 t]
  rw [← Finset.sum_range_reflect
    (fun r => t.choose r * (n - (t + 1) + r - 1).choose r *
      r.factorial * numDerangements (t - r)) (t + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkt : k ≤ t := Finset.mem_range_succ_iff.mp hk
  have hsub : t + 1 - 1 - k = t - k := by omega
  rw [hsub]
  have harg : n - (t + 1) + (t - k) - 1 = n - k - 2 := by omega
  rw [harg]
  have htk : t - (t - k) = k := by omega
  rw [htk]

/-- Each inner sum of the second correction becomes the corresponding signed sum. -/
theorem f2_inner_eq_E_inner (n t : ℕ) (htn : t + 2 ≤ n) :
    (∑ k ∈ Finset.range (t + 1),
      (t.choose (t - k) * (n - k - 2).choose (t - k) *
        (t - k).factorial * numDerangements k : ℤ)) =
    ∑ i ∈ Finset.range (t + 1),
      (-1 : ℤ) ^ i * (Nat.ascFactorial (i + 1) (t - i) : ℤ) *
        ((n - i - 1).choose (t - i) : ℤ) := by
  let a : ℕ → ℤ := fun i =>
    (-1 : ℤ) ^ i * (Nat.ascFactorial (i + 1) (t - i) : ℤ)
  have hterm (k : ℕ) (hk : k ∈ Finset.range (t + 1)) :
      (t.choose (t - k) * (n - k - 2).choose (t - k) *
        (t - k).factorial * numDerangements k : ℤ) =
      ((n - k - 2).choose (t - k) : ℤ) *
        ∑ i ∈ Finset.range (k + 1), a i := by
    have hkt : k ≤ t := Finset.mem_range_succ_iff.mp hk
    rw [numDerangements_sum k]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Finset.mem_range_succ_iff.mp hi
    have hfactor :
        t.choose (t - k) * (t - k).factorial *
          Nat.ascFactorial (i + 1) (k - i) =
        Nat.ascFactorial (i + 1) (t - i) := by
      have hchoose :
          t.choose (t - k) * (t - k).factorial =
            Nat.ascFactorial (k + 1) (t - k) := by
        rw [Nat.ascFactorial_eq_factorial_mul_choose]
        have htk : k + (t - k) = t := by omega
        rw [htk]
        exact Nat.mul_comm _ _
      rw [hchoose]
      have hbase : i + 1 + (k - i) = k + 1 := by omega
      have hlen : (k - i) + (t - k) = t - i := by omega
      rw [Nat.mul_comm, ← hbase, Nat.ascFactorial_mul_ascFactorial,
        hlen]
    dsimp [a]
    have hfactorZ :
        (t.choose (t - k) : ℤ) * ((t - k).factorial : ℤ) *
          (Nat.ascFactorial (i + 1) (k - i) : ℤ) =
        (Nat.ascFactorial (i + 1) (t - i) : ℤ) := by
      exact_mod_cast hfactor
    calc
      _ = ((n - k - 2).choose (t - k) : ℤ) * (-1 : ℤ) ^ i *
            ((t.choose (t - k) : ℤ) * ((t - k).factorial : ℤ) *
              (Nat.ascFactorial (i + 1) (k - i) : ℤ)) := by ring
      _ = _ := by rw [hfactorZ]; ring
  calc
    _ = ∑ k ∈ Finset.range (t + 1),
        ((n - k - 2).choose (t - k) : ℤ) *
          ∑ i ∈ Finset.range (k + 1), a i :=
      Finset.sum_congr rfl hterm
    _ = ∑ i ∈ Finset.range (t + 1),
        ((n - i - 1).choose (t - i) : ℤ) * a i :=
      weighted_hockey_transform n t htn a
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [a]
      ring

/-- The second counting formula has signed correction `E n`. -/
theorem f2_correction_eq_E (n : ℕ) (hn : 1 ≤ n) :
    (numDerangements (n - 1) : ℤ) +
      (∑ m ∈ Finset.Icc 1 (n - 1),
        ∑ r ∈ Finset.range m,
          (m - 1).choose r * (n - m + r - 1).choose r *
            r.factorial * numDerangements (m - 1 - r) : ℕ) = E n := by
  have hbound :
      (∑ i ∈ Finset.range n,
        (-1 : ℤ) ^ i * (Nat.ascFactorial (i + 1) (n - 1 - i) : ℤ) *
          ((n - i - 1).choose (n - 1 - i) : ℤ)) =
        (numDerangements (n - 1) : ℤ) := by
    rw [numDerangements_sum]
    have hnrange : n - 1 + 1 = n := by omega
    rw [hnrange]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have harg : n - i - 1 = n - 1 - i := by omega
    rw [harg, Nat.choose_self]
    ring
  have hE :
      E n =
        (∑ t ∈ Finset.range (n - 1),
          ∑ i ∈ Finset.range (t + 1),
            (-1 : ℤ) ^ i * (Nat.ascFactorial (i + 1) (t - i) : ℤ) *
              ((n - i - 1).choose (t - i) : ℤ)) +
          (numDerangements (n - 1) : ℤ) := by
    unfold E
    conv_lhs => rw [show n = n - 1 + 1 by omega, Finset.sum_range_succ]
    rw [show n - 1 + 1 = n by omega]
    rw [hbound]
  have hre := congrArg (fun x : ℕ => (x : ℤ)) (f2_correction_reindexed n)
  calc
    _ = (numDerangements (n - 1) : ℤ) +
        ∑ t ∈ Finset.range (n - 1),
          ∑ k ∈ Finset.range (t + 1),
            (t.choose (t - k) * (n - k - 2).choose (t - k) *
              (t - k).factorial * numDerangements k : ℤ) := by
                  rw [hre]
                  simp only [Nat.cast_sum, Nat.cast_mul]
    _ = (numDerangements (n - 1) : ℤ) +
        ∑ t ∈ Finset.range (n - 1),
          ∑ i ∈ Finset.range (t + 1),
            (-1 : ℤ) ^ i * (Nat.ascFactorial (i + 1) (t - i) : ℤ) *
              ((n - i - 1).choose (t - i) : ℤ) := by
            congr 1
            apply Finset.sum_congr rfl
            intro t ht
            apply f2_inner_eq_E_inner n t
            have := Finset.mem_range.mp ht
            omega
    _ = E n := by rw [hE]; ring

/-- Reindex the first correction and separate its nested subset choices. -/
theorem f1_correction_reindexed (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n,
      ∑ k ∈ Finset.range (n - m + 1),
        (n - m).choose k * (m + k - 1).choose (n - m) * numDerangements k) =
    ∑ t ∈ Finset.range n,
      ∑ k ∈ Finset.range (t + 1),
        (n - t + k - 1).choose k * (n - t - 1).choose (t - k) *
          numDerangements k := by
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  rw [← Finset.sum_range_reflect
    (fun j => ∑ k ∈ Finset.range (n - (1 + j) + 1),
      (n - (1 + j)).choose k * (1 + j + k - 1).choose (n - (1 + j)) *
        numDerangements k) n]
  apply Finset.sum_congr rfl
  intro t ht
  have htn : t < n := Finset.mem_range.mp ht
  have hm : 1 + (n - 1 - t) = n - t := by omega
  rw [hm]
  have hnm : n - (n - t) = t := by omega
  rw [hnm]
  apply Finset.sum_congr rfl
  intro k hk
  have hkt : k ≤ t := Finset.mem_range_succ_iff.mp hk
  have htop : n - t + k - 1 - k = n - t - 1 := by omega
  rw [Nat.mul_comm (t.choose k), Nat.choose_mul hkt, htop]

/-- The positive polynomial transform in the first formula, with `p = n - t - 1`. -/
def positiveTransform (p t : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (t + 1),
    (p + k).choose k * p.choose (t - k) * numDerangements k

/-- Pascal's rule gives a finite recurrence for the positive transform. -/
theorem positiveTransform_recurrence (p t : ℕ) :
    (p + 1) * positiveTransform (p + 1) (t + 1) =
      (p + t + 2) * positiveTransform p (t + 1) +
        (t + 1) * positiveTransform p t := by
  let f := fun p t k : ℕ =>
    (p + k).choose k * p.choose (t - k) * numDerangements k
  have hbulk (k : ℕ) (hk : k ∈ Finset.range (t + 1)) :
      (p + 1) * f (p + 1) (t + 1) k =
        (p + t + 2) * f p (t + 1) k + (t + 1) * f p t k := by
    have hkt : k ≤ t := Finset.mem_range_succ_iff.mp hk
    let r := t + 1 - k
    have hr : 1 ≤ r := by dsimp [r]; omega
    have htk : t - k = r - 1 := by dsimp [r]; omega
    have hsucc : (p + 1 + k).choose k * (p + 1) =
        (p + k).choose k * (p + k + 1) := by
      have harg : p + k + 1 - k = p + 1 := by omega
      have h := Nat.choose_mul_succ_eq (p + k) k
      rw [harg] at h
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm
    have hpascal : (p + 1).choose r = p.choose r + p.choose (r - 1) := by
      obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      rw [hq]
      simpa [Nat.add_comm] using Nat.choose_succ_succ' p q
    have hweight : (p + 1) * p.choose (r - 1) =
        r * (p + 1).choose r := by
      obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      rw [hq]
      simpa [Nat.mul_comm] using Nat.add_one_mul_choose_eq p q
    have htr : t + 1 = k + r := by dsimp [r]; omega
    have hcore :
        (p + k + 1) * (p + 1).choose r =
          (p + t + 2) * p.choose r + (t + 1) * p.choose (r - 1) := by
      have hweight' :
          (p + 1) * p.choose (r - 1) =
            r * (p.choose r + p.choose (r - 1)) := by
        rw [← hpascal]
        exact hweight
      rw [htr]
      nlinarith [hweight']
    dsimp [f]
    rw [show t + 1 - k = r by rfl, htk]
    calc
      _ = ((p + k).choose k * (p + k + 1)) * (p + 1).choose r *
            numDerangements k := by rw [← hsucc]; ring
      _ = (p + t + 2) * ((p + k).choose k * p.choose r * numDerangements k) +
          (t + 1) * ((p + k).choose k * p.choose (r - 1) *
            numDerangements k) := by
            calc
              _ = (p + k).choose k *
                    ((p + k + 1) * (p + 1).choose r) * numDerangements k := by ring
              _ = (p + k).choose k *
                    ((p + t + 2) * p.choose r + (t + 1) * p.choose (r - 1)) *
                    numDerangements k := by rw [hcore]
              _ = _ := by ring
  have hlast :
      (p + 1) * f (p + 1) (t + 1) (t + 1) =
        (p + t + 2) * f p (t + 1) (t + 1) := by
    dsimp [f]
    simp only [Nat.sub_self, Nat.choose_zero_right, mul_one]
    have hsucc := Nat.choose_mul_succ_eq (p + t + 1) (t + 1)
    have harg : p + t + 1 + 1 - (t + 1) = p + 1 := by omega
    rw [harg] at hsucc
    calc
      _ = ((p + 1) * (p + t + 2).choose (t + 1)) *
            numDerangements (t + 1) := by ring_nf
      _ = ((p + t + 2) * (p + t + 1).choose (t + 1)) *
            numDerangements (t + 1) := by
            congr 1
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using hsucc.symm
      _ = _ := by ring_nf
  change (p + 1) * (∑ k ∈ Finset.range (t + 2), f (p + 1) (t + 1) k) =
    (p + t + 2) * (∑ k ∈ Finset.range (t + 2), f p (t + 1) k) +
      (t + 1) * (∑ k ∈ Finset.range (t + 1), f p t k)
  calc
    _ = ∑ k ∈ Finset.range (t + 2), (p + 1) * f (p + 1) (t + 1) k := by
      rw [Finset.mul_sum]
    _ = (∑ k ∈ Finset.range (t + 1), (p + 1) * f (p + 1) (t + 1) k) +
          (p + 1) * f (p + 1) (t + 1) (t + 1) := by
      rw [Finset.sum_range_succ]
    _ = (∑ k ∈ Finset.range (t + 1),
          ((p + t + 2) * f p (t + 1) k + (t + 1) * f p t k)) +
          (p + t + 2) * f p (t + 1) (t + 1) := by
      rw [Finset.sum_congr rfl hbulk, hlast]
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_range_succ (f p (t + 1)) (t + 1)]
      ring

/-- The signed polynomial transform in equation (4.5), with `p = n - t - 1`. -/
def signedTransform (p t : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (t + 1),
    (-1 : ℤ) ^ i * (Nat.ascFactorial (i + 1) (t - i) : ℤ) *
      ((p + t - i).choose (t - i) : ℤ)

/-- The signed transform has the same finite recurrence as the positive transform. -/
theorem signedTransform_recurrence (p t : ℕ) :
    (p + 1 : ℤ) * signedTransform (p + 1) (t + 1) =
      (p + t + 2 : ℤ) * signedTransform p (t + 1) +
        (t + 1 : ℤ) * signedTransform p t := by
  let g := fun p t i : ℕ =>
    (-1 : ℤ) ^ i * (Nat.ascFactorial (i + 1) (t - i) : ℤ) *
      ((p + t - i).choose (t - i) : ℤ)
  have hzero :
      (p + 1 : ℤ) * g (p + 1) (t + 1) 0 =
        (p + t + 2 : ℤ) * g p (t + 1) 0 := by
    dsimp [g]
    simp only [one_mul]
    have h := Nat.choose_mul_succ_eq (p + t + 1) (t + 1)
    have harg : p + t + 1 + 1 - (t + 1) = p + 1 := by omega
    rw [harg] at h
    have hZ :
        (p + 1 : ℤ) * ((p + t + 2).choose (t + 1) : ℤ) =
          (p + t + 2 : ℤ) * ((p + t + 1).choose (t + 1) : ℤ) := by
      exact_mod_cast (by simpa [Nat.mul_comm, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h.symm)
    have htop : p + 1 + (t + 1) = p + t + 2 := by omega
    have htop' : p + (t + 1) = p + t + 1 := by omega
    rw [htop, htop']
    calc
      _ = (Nat.ascFactorial 1 (t + 1) : ℤ) *
            ((p + 1 : ℤ) * ((p + t + 2).choose (t + 1) : ℤ)) := by ring
      _ = (Nat.ascFactorial 1 (t + 1) : ℤ) *
            ((p + t + 2 : ℤ) * ((p + t + 1).choose (t + 1) : ℤ)) := by rw [hZ]
      _ = _ := by ring
  have hshift (j : ℕ) (hj : j ∈ Finset.range (t + 1)) :
      (p + 1 : ℤ) * g (p + 1) (t + 1) (j + 1) =
        (p + t + 2 : ℤ) * g p (t + 1) (j + 1) +
          (t + 1 : ℤ) * g p t j := by
    have hjt : j ≤ t := Finset.mem_range_succ_iff.mp hj
    let r := t - j
    have htr : j + 1 + r = t + 1 := by dsimp [r]; omega
    have hsub : t + 1 - (j + 1) = r := by dsimp [r]; omega
    have hfac :
        (j + 1) * Nat.ascFactorial (j + 2) r =
          (t + 1) * Nat.ascFactorial (j + 1) r := by
      have h := Nat.succ_ascFactorial (j + 1) r
      rw [htr] at h
      simpa [Nat.add_assoc] using h
    have hfacZ :
        (j + 1 : ℤ) * (Nat.ascFactorial (j + 2) r : ℤ) =
          (t + 1 : ℤ) * (Nat.ascFactorial (j + 1) r : ℤ) := by
      exact_mod_cast hfac
    have hchoose :
        (p + 1 : ℤ) * ((p + 1 + r).choose r : ℤ) =
          (p + r + 1 : ℤ) * ((p + r).choose r : ℤ) := by
      have h := Nat.choose_mul_succ_eq (p + r) r
      have harg : p + r + 1 - r = p + 1 := by omega
      rw [harg] at h
      exact_mod_cast (by simpa [Nat.mul_comm, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h.symm)
    dsimp [g]
    rw [hsub, show t - j = r by rfl]
    have hpSub : p + (t + 1) - (j + 1) = p + r := by omega
    have hpSub' : p + 1 + (t + 1) - (j + 1) = p + 1 + r := by omega
    rw [hpSub, hpSub']
    simp only [pow_succ]
    have hsum : (p + t + 2 : ℤ) = (p + r + 1 : ℤ) + (j + 1 : ℤ) := by
      exact_mod_cast (by omega : p + t + 2 = p + r + 1 + (j + 1))
    rw [hsum]
    have hbase : p + t - j = p + r := by omega
    rw [hbase]
    calc
      _ = -(((-1 : ℤ) ^ j) * (Nat.ascFactorial (j + 2) r : ℤ) *
            ((p + 1 : ℤ) * ((p + 1 + r).choose r : ℤ))) := by ring
      _ = -(((-1 : ℤ) ^ j) * (Nat.ascFactorial (j + 2) r : ℤ) *
            ((p + r + 1 : ℤ) * ((p + r).choose r : ℤ))) := by rw [hchoose]
      _ = ((p + r + 1 : ℤ) + (j + 1 : ℤ)) *
            ((-1 : ℤ) ^ j * -1 * (Nat.ascFactorial (j + 2) r : ℤ) *
              ((p + r).choose r : ℤ)) +
          (-1 : ℤ) ^ j * ((p + r).choose r : ℤ) *
            ((j + 1 : ℤ) * (Nat.ascFactorial (j + 2) r : ℤ)) := by ring
      _ = _ := by rw [hfacZ]; ring
  change (p + 1 : ℤ) * (∑ i ∈ Finset.range (t + 2), g (p + 1) (t + 1) i) =
    (p + t + 2 : ℤ) * (∑ i ∈ Finset.range (t + 2), g p (t + 1) i) +
      (t + 1 : ℤ) * (∑ i ∈ Finset.range (t + 1), g p t i)
  calc
    _ = ∑ i ∈ Finset.range (t + 2), (p + 1 : ℤ) * g (p + 1) (t + 1) i := by
      rw [Finset.mul_sum]
    _ = (∑ j ∈ Finset.range (t + 1),
          (p + 1 : ℤ) * g (p + 1) (t + 1) (j + 1)) +
          (p + 1 : ℤ) * g (p + 1) (t + 1) 0 := by
      rw [Finset.sum_range_succ']
    _ = (∑ j ∈ Finset.range (t + 1),
          ((p + t + 2 : ℤ) * g p (t + 1) (j + 1) +
            (t + 1 : ℤ) * g p t j)) +
          (p + t + 2 : ℤ) * g p (t + 1) 0 := by
      rw [Finset.sum_congr rfl hshift, hzero]
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_range_succ' (g p (t + 1)) (t + 1)]
      ring

/-- The finite derangement transform equates the positive and signed inner sums. -/
theorem positiveTransform_eq_signedTransform (p t : ℕ) :
    (positiveTransform p t : ℤ) = signedTransform p t := by
  induction p generalizing t with
  | zero =>
      have hpositive : positiveTransform 0 t = numDerangements t := by
        unfold positiveTransform
        rw [Finset.sum_eq_single t]
        · simp
        · intro k hk hne
          have hkt : k ≤ t := Finset.mem_range_succ_iff.mp hk
          have hpos : 0 < t - k := by omega
          rw [Nat.choose_eq_zero_of_lt hpos]
          simp
        · intro h
          simp at h
      have hsigned : signedTransform 0 t = (numDerangements t : ℤ) := by
        rw [signedTransform, numDerangements_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp
      exact (congrArg (fun x : ℕ => (x : ℤ)) hpositive).trans hsigned.symm
  | succ p ih =>
      cases t with
      | zero =>
          simp [positiveTransform, signedTransform]
      | succ t =>
          have hp := congrArg (fun x : ℕ => (x : ℤ))
            (positiveTransform_recurrence p t)
          simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hp
          rw [ih (t + 1), ih t] at hp
          have hs := signedTransform_recurrence p t
          have hmul :
              (p + 1 : ℤ) * (positiveTransform (p + 1) (t + 1) : ℤ) =
                (p + 1 : ℤ) * signedTransform (p + 1) (t + 1) := by
            exact hp.trans hs.symm
          exact mul_left_cancel₀ (by omega : (p + 1 : ℤ) ≠ 0) hmul

/-- The first counting formula has the same signed correction `E n`. -/
theorem f1_correction_eq_E (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n,
      ∑ k ∈ Finset.range (n - m + 1),
        (n - m).choose k * (m + k - 1).choose (n - m) *
          numDerangements k : ℕ) = E n := by
  have hre := congrArg (fun x : ℕ => (x : ℤ)) (f1_correction_reindexed n)
  calc
    _ = ∑ t ∈ Finset.range n, (positiveTransform (n - t - 1) t : ℤ) := by
      rw [hre]
      simp only [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have htn : t < n := Finset.mem_range.mp ht
      have hterm :
          (∑ k ∈ Finset.range (t + 1),
            (n - t + k - 1).choose k * (n - t - 1).choose (t - k) *
              numDerangements k) = positiveTransform (n - t - 1) t := by
        unfold positiveTransform
        apply Finset.sum_congr rfl
        intro k hk
        have harg : n - t + k - 1 = n - t - 1 + k := by omega
        rw [harg]
      simpa only [Nat.cast_sum] using
        congrArg (fun x : ℕ => (x : ℤ)) hterm
    _ = ∑ t ∈ Finset.range n, signedTransform (n - t - 1) t := by
      apply Finset.sum_congr rfl
      intro t ht
      exact positiveTransform_eq_signedTransform (n - t - 1) t
    _ = E n := by
      unfold E signedTransform
      apply Finset.sum_congr rfl
      intro t ht
      have htn : t < n := Finset.mem_range.mp ht
      apply Finset.sum_congr rfl
      intro i hi
      have hit : i ≤ t := Finset.mem_range_succ_iff.mp hi
      have harg : n - t - 1 + t - i = n - i - 1 := by omega
      rw [harg]

end D5.S3.Combinatorics.ArrowWilfSums

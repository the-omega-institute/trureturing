/- GID: D5/S3/Combinatorics/OddIndependence/OddGridCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OddIndependence/OddGridCounting
   mirror-E: none(waiver:finite-window-counting)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A finitely supported padded grid is counted nine times by its three-square windows. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OddIndependence.OddGridCounting

open Finset

private theorem sum_shift_of_support (m k : ℕ) (f : ℕ → ℤ)
    (hl : ∀ i, i < k → f i = 0) (hu : ∀ i, m ≤ i → f i = 0) :
    (∑ i ∈ range m, f (i + k)) = ∑ i ∈ range m, f i := by
  have h₁ := sum_range_add f k m
  have h₂ := sum_range_add f m k
  have hz₁ : (∑ i ∈ range k, f i) = 0 :=
    sum_eq_zero fun i hi => hl i (mem_range.mp hi)
  have hz₂ : (∑ i ∈ range k, f (m + i)) = 0 :=
    sum_eq_zero fun i _ => hu (m + i) (Nat.le_add_right m i)
  rw [hz₁, zero_add] at h₁
  rw [hz₂, add_zero] at h₂
  simpa only [Nat.add_comm] using h₁.symm.trans (by simpa [Nat.add_comm] using h₂)

theorem ninefold_count (n : ℕ) (b : ℕ → ℕ → Bool)
    (hs : ∀ x y, b x y = true → 2 ≤ x ∧ x < n + 2 ∧ 2 ≤ y ∧ y < n + 2) :
    (∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2),
      ∑ r ∈ range 3, ∑ c ∈ range 3, (if b (i + r) (j + c) then (1 : ℤ) else 0)) =
      9 * (∑ x ∈ range (n + 2), ∑ y ∈ range (n + 2),
        (if b x y then (1 : ℤ) else 0)) := by
  have shift₁ (y r : ℕ) (hr : r < 3) :
      (∑ i ∈ range (n + 2), (if b (i + r) y then (1 : ℤ) else 0)) =
        ∑ i ∈ range (n + 2), (if b i y then (1 : ℤ) else 0) := by
    apply sum_shift_of_support (n + 2) r (fun i => if b i y then 1 else 0)
    · intro i hi
      have hb : b i y = false := by
        cases h : b i y with
        | false => rfl
        | true => have := (hs i y h).1; omega
      simp [hb]
    · intro i hi
      have hb : b i y = false := by
        cases h : b i y with
        | false => rfl
        | true => have := (hs i y h).2.1; omega
      simp [hb]
  have shift₂ (x c : ℕ) (hc : c < 3) :
      (∑ j ∈ range (n + 2), (if b x (j + c) then (1 : ℤ) else 0)) =
        ∑ j ∈ range (n + 2), (if b x j then (1 : ℤ) else 0) := by
    apply sum_shift_of_support (n + 2) c (fun j => if b x j then 1 else 0)
    · intro j hj
      have hb : b x j = false := by
        cases h : b x j with
        | false => rfl
        | true => have := (hs x j h).2.2.1; omega
      simp [hb]
    · intro j hj
      have hb : b x j = false := by
        cases h : b x j with
        | false => rfl
        | true => have := (hs x j h).2.2.2; omega
      simp [hb]
  calc
    _ = ∑ i ∈ range (n + 2), ∑ r ∈ range 3,
        ∑ j ∈ range (n + 2), ∑ c ∈ range 3,
          (if b (i + r) (j + c) then (1 : ℤ) else 0) := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ r ∈ range 3, ∑ i ∈ range (n + 2),
        ∑ j ∈ range (n + 2), ∑ c ∈ range 3,
          (if b (i + r) (j + c) then (1 : ℤ) else 0) := by rw [sum_comm]
    _ = ∑ r ∈ range 3, ∑ i ∈ range (n + 2),
        ∑ c ∈ range 3, ∑ j ∈ range (n + 2),
          (if b (i + r) (j + c) then (1 : ℤ) else 0) := by
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ r ∈ range 3, ∑ c ∈ range 3,
        ∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2),
          (if b (i + r) (j + c) then (1 : ℤ) else 0) := by
      apply sum_congr rfl
      intro r _
      rw [sum_comm]
    _ = ∑ r ∈ range 3, ∑ c ∈ range 3,
        ∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2),
          (if b i j then (1 : ℤ) else 0) := by
      apply sum_congr rfl
      intro r hr
      apply sum_congr rfl
      intro c hc
      simp_rw [shift₂ _ c (mem_range.mp hc)]
      rw [sum_comm]
      simp_rw [shift₁ _ r (mem_range.mp hr)]
      rw [sum_comm]
    _ = _ := by simp; ring

end D5.S3.Combinatorics.OddIndependence.OddGridCounting

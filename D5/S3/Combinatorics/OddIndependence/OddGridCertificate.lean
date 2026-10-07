/- GID: D5/S3/Combinatorics/OddIndependence/OddGridCertificate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OddIndependence/OddGridCertificate
   mirror-E: none(waiver:local-discharge-certificate)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: A telescoping local discharge bounds every cross-free padded independent grid. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OddIndependence.OddGridCertificate

open Finset

private def H : Bool → Bool → Bool → Bool → Bool → Bool → ℤ
  | true, false, false, false, true, false => -1
  | false, false, false, true, true, false => 1
  | true, false, false, true, true, false => -5
  | false, true, true, false, false, true => 5
  | _, _, _, _, _, _ => 0

private def V : Bool → Bool → Bool → Bool → Bool → Bool → ℤ
  | true, false, false, false, true, false => 3
  | false, false, true, false, true, false => 2
  | false, false, false, true, false, true => 4
  | false, true, false, true, false, true => 3
  | _, _, _, _, _, _ => 0

theorem certificate_bound (n : ℕ) (b : ℕ → ℕ → Bool)
    (hs : ∀ x y, b x y = true →
      2 ≤ x ∧ x < n + 2 ∧ 2 ≤ y ∧ y < n + 2)
    (hi : ∀ x y, (b x y = true → b (x + 1) y = false) ∧
      (b x y = true → b x (y + 1) = false))
    (hc : ∀ x y, ¬ (b x (y + 1) = true ∧ b (x + 1) y = true ∧
      b (x + 1) (y + 2) = true ∧ b (x + 2) (y + 1) = true)) :
    8 * (∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2),
      ∑ r ∈ range 3, ∑ c ∈ range 3,
        (if b (i + r) (j + c) then (1 : ℤ) else 0)) ≤ 27 * (n + 2) ^ 2 := by
  have check : ∀ a b c d e f g h k : Bool,
      (a = true → b = false) → (b = true → c = false) →
      (d = true → e = false) → (e = true → f = false) →
      (g = true → h = false) → (h = true → k = false) →
      (a = true → d = false) → (d = true → g = false) →
      (b = true → e = false) → (e = true → h = false) →
      (c = true → f = false) → (f = true → k = false) →
      ¬ (b = true ∧ d = true ∧ f = true ∧ h = true) →
      8 * ((if a then (1 : ℤ) else 0) + (if b then 1 else 0) +
        (if c then 1 else 0) + (if d then 1 else 0) + (if e then 1 else 0) +
        (if f then 1 else 0) + (if g then 1 else 0) + (if h then 1 else 0) +
        (if k then 1 else 0)) + H a b d e g h - H b c e f h k +
        V a b c d e f - V d e f g h k ≤ 27 := by
    set_option synthInstance.maxSize 100000 in
      decide
  let hf := fun i j => H (b i j) (b i (j + 1))
    (b (i + 1) j) (b (i + 1) (j + 1)) (b (i + 2) j) (b (i + 2) (j + 1))
  let vf := fun i j => V (b i j) (b i (j + 1)) (b i (j + 2))
    (b (i + 1) j) (b (i + 1) (j + 1)) (b (i + 1) (j + 2))
  have window (i j : ℕ) :
      8 * (∑ r ∈ range 3, ∑ c ∈ range 3,
        (if b (i + r) (j + c) then (1 : ℤ) else 0)) +
      hf i j - hf i (j + 1) + vf i j - vf (i + 1) j ≤ 27 := by
    have ht := check (b i j) (b i (j + 1)) (b i (j + 2))
      (b (i + 1) j) (b (i + 1) (j + 1)) (b (i + 1) (j + 2))
      (b (i + 2) j) (b (i + 2) (j + 1)) (b (i + 2) (j + 2))
      (hi i j).2 (hi i (j + 1)).2 (hi (i + 1) j).2
      (hi (i + 1) (j + 1)).2 (hi (i + 2) j).2 (hi (i + 2) (j + 1)).2
      (hi i j).1 (hi (i + 1) j).1 (hi i (j + 1)).1
      (hi (i + 1) (j + 1)).1 (hi i (j + 2)).1 (hi (i + 1) (j + 2)).1
      (hc i j)
    simpa only [hf, vf, sum_range_succ, sum_range_zero, add_zero, zero_add,
      Nat.add_zero, Nat.reduceAdd, Nat.add_assoc, add_assoc] using ht
  have zero (x y : ℕ) (h : x < 2 ∨ n + 2 ≤ x ∨ y < 2 ∨ n + 2 ≤ y) :
      b x y = false := by
    cases hb : b x y with
    | false => rfl
    | true => have ht := hs x y hb; omega
  have hz (i : ℕ) : hf i 0 = 0 ∧ hf i (n + 2) = 0 := by
    constructor <;> simp [hf, zero, H]
  have vz (j : ℕ) : vf 0 j = 0 ∧ vf (n + 2) j = 0 := by
    constructor <;> simp [vf, zero, V]
  have telescope (f : ℕ → ℤ) (m : ℕ) :
      (∑ i ∈ range m, (f i - f (i + 1))) = f 0 - f m := by
    exact sum_range_sub' f m
  have hsum : (∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2),
      (hf i j - hf i (j + 1))) = 0 := by
    apply sum_eq_zero
    intro i _
    rw [telescope]
    simp [(hz i).1, (hz i).2]
  have vsum : (∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2),
      (vf i j - vf (i + 1) j)) = 0 := by
    rw [sum_comm]
    apply sum_eq_zero
    intro j _
    rw [telescope]
    simp [(vz j).1, (vz j).2]
  have total := sum_le_sum fun i (_ : i ∈ range (n + 2)) =>
    sum_le_sum fun j (_ : j ∈ range (n + 2)) => window i j
  have hsum' : (∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2), hf i j) -
      (∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2), hf i (j + 1)) = 0 := by
    simpa [sum_sub_distrib] using hsum
  have vsum' : (∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2), vf i j) -
      (∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2), vf (i + 1) j) = 0 := by
    simpa [sum_sub_distrib] using vsum
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum,
    sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat] at total
  nlinarith [hsum', vsum']

end D5.S3.Combinatorics.OddIndependence.OddGridCertificate

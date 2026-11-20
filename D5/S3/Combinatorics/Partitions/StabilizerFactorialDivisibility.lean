/- GID: D5/S3/Combinatorics/Partitions/StabilizerFactorialDivisibility
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/StabilizerFactorialDivisibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A factorial product divides each scaled block mass when the total mass is divisible by one less than the number of labels. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Multinomial

namespace D5.S3.Combinatorics.Partitions.StabilizerFactorialDivisibility

set_option autoImplicit false

open Finset
open scoped Nat

private def removeOne {I : Type*} [DecidableEq I] (s : I → ℕ) (i : I) : I → ℕ :=
  Function.update s i (s i - 1)

private theorem removeOne_mass {I : Type*} [Fintype I] [DecidableEq I]
    (s v : I → ℕ) (i : I) (hi : 0 < s i) :
    (∑ j, removeOne s i j * v j) + v i = ∑ j, s j * v j := by
  have outside : (∑ j ∈ univ.erase i, removeOne s i j * v j) =
      ∑ j ∈ univ.erase i, s j * v j := by
    apply sum_congr rfl
    intro j hj
    simp only [removeOne, Function.update_of_ne (ne_of_mem_erase hj)]
  have inside : removeOne s i i * v i + v i = s i * v i := by
    have eq := congrArg (· * v i) (Nat.sub_add_cancel hi)
    simpa only [removeOne, Function.update_self, Nat.add_mul, Nat.one_mul] using eq
  calc
    _ = ((∑ j ∈ univ.erase i, removeOne s i j * v j) + removeOne s i i * v i) + v i := by
      rw [sum_erase_add _ (fun j => removeOne s i j * v j) (mem_univ i)]
    _ = (∑ j ∈ univ.erase i, s j * v j) + s i * v i := by rw [outside, add_assoc, inside]
    _ = _ := sum_erase_add _ (fun j => s j * v j) (mem_univ i)

private theorem removeOne_size {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℕ) (i : I) (hi : 0 < s i) : ∑ j, removeOne s i j = (∑ j, s j) - 1 := by
  have eq := removeOne_mass s (fun _ => 1) i hi
  simp only [Nat.mul_one] at eq
  omega

private theorem removeOne_factorials {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℕ) (i : I) (hi : 0 < s i) :
    (∏ j, (removeOne s i j)!) * s i = ∏ j, (s j)! := by
  have outside : (∏ j ∈ univ.erase i, (removeOne s i j)!) = ∏ j ∈ univ.erase i, (s j)! := by
    apply prod_congr rfl
    intro j hj
    simp only [removeOne, Function.update_of_ne (ne_of_mem_erase hj)]
  have inside : (removeOne s i i)! * s i = (s i)! := by
    simp only [removeOne, Function.update_self]
    calc
      _ = ((s i - 1) + 1)! := by rw [Nat.factorial_succ, Nat.mul_comm, Nat.sub_add_cancel hi]
      _ = _ := by rw [Nat.sub_add_cancel hi]
  calc
    _ = ((∏ j ∈ univ.erase i, (removeOne s i j)!) * (removeOne s i i)!) * s i := by
      rw [prod_erase_mul _ (fun j => (removeOne s i j)!) (mem_univ i)]
    _ = (∏ j ∈ univ.erase i, (s j)!) * (s i)! := by rw [outside, mul_assoc, inside]
    _ = _ := prod_erase_mul _ (fun j => (s j)!) (mem_univ i)

/-- The block factorial product divides each scaled block mass when the total mass
is divisible by one less than the number of labels. -/
theorem factorial_product_dvd_scaled_coordinate {I : Type*} [Fintype I]
    {k : ℕ} (hk : 2 ≤ k) (s v : I → ℕ) (total : ∑ i, s i = k)
    (divisible : k-1 ∣ ∑ i, s i * v i) (i : I) :
    (∏ j, (s j)!) ∣ (k-2)! * (s i * v i) := by
  classical
  by_cases hsi : s i = 0
  · simp [hsi]
  let b := removeOne s i
  let P := ∏ j, (b j)!
  let D := (k-2)!
  have size : ∑ j, b j = k-1 := (removeOne_size s i (Nat.pos_of_ne_zero hsi)).trans (congrArg (· - 1) total)
  have shorter : P ∣ D*(k-1) := by
    have h := Nat.prod_factorial_dvd_factorial_sum univ b
    rw [size] at h
    have fact : (k-1)! = D*(k-1) := by
      calc
        _ = ((k-2)+1)! := by congr 1; omega
        _ = _ := by rw [Nat.factorial_succ, Nat.mul_comm, show k-2+1 = k-1 by omega]
    exact fact ▸ h
  have each : ∀ j, P ∣ D * b j := by
    intro j
    by_cases zero : b j = 0
    · simp [zero]
    have positive := Nat.pos_of_ne_zero zero
    have h := Nat.prod_factorial_dvd_factorial_sum univ (removeOne b j)
    have size' : (∑ l, removeOne b j l) = k-2 := by
      rw [removeOne_size b j positive, size]
      omega
    rw [size'] at h
    have scale := Nat.mul_dvd_mul_right h (b j)
    simpa only [removeOne_factorials b j positive] using scale
  have whole : P ∣ D * (∑ j, s j * v j) := by
    obtain ⟨c,hc⟩ := divisible
    rw [hc, ← Nat.mul_assoc]
    exact dvd_mul_of_dvd_left shorter _
  have remainder : P ∣ D * (∑ j, b j * v j) := by
    rw [Finset.mul_sum]
    apply Finset.dvd_sum
    intro j _
    rw [← Nat.mul_assoc]
    exact dvd_mul_of_dvd_left (each j) _
  have hmass : (∑ j, b j * v j) + v i = ∑ j, s j * v j :=
    removeOne_mass s v i (Nat.pos_of_ne_zero hsi)
  rw [← hmass, Nat.mul_add] at whole
  have single : P ∣ D * v i := by
    have minus := Nat.dvd_sub whole remainder
    rwa [Nat.add_sub_cancel_left] at minus
  have scale := Nat.mul_dvd_mul_right single (s i)
  rw [removeOne_factorials s i (Nat.pos_of_ne_zero hsi)] at scale
  simpa only [Nat.mul_assoc, Nat.mul_comm (v i) (s i)] using scale

end D5.S3.Combinatorics.Partitions.StabilizerFactorialDivisibility

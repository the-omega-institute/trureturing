/- GID: D5/S3/Combinatorics/GroupWords/InvolutionExactLength
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GroupWords/InvolutionExactLength
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Group.Pointwise.Set.Basic]
   utility: none
   digest: Exact-length involution products have bounded parity-specific powers. -/

import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Order.Interval.Set.Basic
import Lean.Elab.Tactic.Omega

/-! # Exact-length products of two involutions

No distinctness, infinite-order or injectivity hypothesis is required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GroupWords.InvolutionExactLength

open scoped Pointwise

private theorem cyclic_steps {G : Type*} [Group G] (g : G) (m : ℕ) :
    ({1, g, g⁻¹} : Set G) ^ m =
      (fun k : ℤ => g ^ k) '' Set.Icc (-(m : ℤ)) m := by
  induction m with
  | zero => simp [Set.singleton_one]
  | succ m ih =>
    rw [pow_succ, ih]
    ext x
    constructor
    · rintro ⟨a, ⟨k, hk, rfl⟩, b, hb, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl
      · exact ⟨k, by simp only [Set.mem_Icc] at *; simp only [Nat.cast_succ]; omega, by simp⟩
      · refine ⟨k + 1, ?_, ?_⟩
        · simp only [Set.mem_Icc] at *; simp only [Nat.cast_succ]; omega
        · simp [zpow_add]
      · refine ⟨k - 1, ?_, ?_⟩
        · simp only [Set.mem_Icc] at *; simp only [Nat.cast_succ]; omega
        · simp [zpow_sub]
    · rintro ⟨k, hk, rfl⟩
      simp only [Set.mem_Icc, Nat.cast_add, Nat.cast_one] at hk
      by_cases hlo : k < -(m : ℤ)
      · refine ⟨g ^ (k + 1), ⟨k + 1, by simp only [Set.mem_Icc]; omega, rfl⟩,
          g⁻¹, by simp, ?_⟩
        simp [zpow_add]
      · by_cases hhi : (m : ℤ) < k
        · refine ⟨g ^ (k - 1), ⟨k - 1, by simp only [Set.mem_Icc]; omega, rfl⟩,
            g, by simp, ?_⟩
          simp [zpow_sub]
        · exact ⟨g ^ k, ⟨k, ⟨by omega, by omega⟩, rfl⟩, 1, by simp, by simp⟩

/-- Exact-length products retain both the parity and the reachable exponent endpoints. -/
theorem exact_length_products {G : Type*} [Group G] (u v : G)
    (hu : u * u = 1) (hv : v * v = 1) (m : ℕ) :
    ({u, v} : Set G) ^ (2 * m) =
        (fun k : ℤ => (u * v) ^ k) '' Set.Icc (-(m : ℤ)) m ∧
      ({u, v} : Set G) ^ (2 * m + 1) =
        (fun k : ℤ => u * (u * v) ^ k) '' Set.Icc (-(m : ℤ)) (m + 1) := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv
  have hi : (u * v)⁻¹ = v * u := by simp [hui, hvi]
  have hs : ({u, v} : Set G) ^ 2 = {1, u * v, (u * v)⁻¹} := by
    rw [pow_two]
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hu, hv, hi]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨u, by simp, u, by simp, hu⟩
      · exact ⟨u, by simp, v, by simp, rfl⟩
      · exact ⟨v, by simp, u, by simp, hi.symm⟩
  have he : ({u, v} : Set G) ^ (2 * m) =
      (fun k : ℤ => (u * v) ^ k) '' Set.Icc (-(m : ℤ)) m := by
    rw [pow_mul, hs, cyclic_steps]
  refine ⟨he, ?_⟩
  rw [pow_succ', he]
  have huv : u * (u * v) = v := by rw [← mul_assoc, hu, one_mul]
  ext x
  constructor
  · rintro ⟨a, ha, b, ⟨k, hk, rfl⟩, rfl⟩
    change -(m : ℤ) ≤ k ∧ k ≤ m at hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with ha | ha <;> subst a
    · exact ⟨k, ⟨hk.1, by omega⟩, rfl⟩
    · refine ⟨k + 1, ⟨by omega, by omega⟩, ?_⟩
      change u * (u * v) ^ (k + 1) = v * (u * v) ^ k
      rw [show k + 1 = 1 + k by omega, zpow_add, zpow_one, ← mul_assoc, huv]
  · rintro ⟨k, hk, rfl⟩
    change -(m : ℤ) ≤ k ∧ k ≤ m + 1 at hk
    by_cases h : k ≤ (m : ℤ)
    · exact ⟨u, by simp, (u * v) ^ k, ⟨k, ⟨hk.1, h⟩, rfl⟩, rfl⟩
    · refine ⟨v, by simp, (u * v) ^ (k - 1),
        ⟨k - 1, ⟨by omega, by omega⟩, rfl⟩, ?_⟩
      change v * (u * v) ^ (k - 1) = u * (u * v) ^ k
      calc
        v * (u * v) ^ (k - 1) = (u * (u * v)) * (u * v) ^ (k - 1) := congrArg (fun a => a * (u * v) ^ (k - 1)) huv.symm
        _ = u * (u * v) ^ k := by
          rw [mul_assoc]
          congr 1
          calc
            (u * v) * (u * v) ^ (k - 1) = (u * v) ^ (1 + (k - 1)) := by rw [zpow_add, zpow_one]
            _ = (u * v) ^ k := by congr 1; omega

end D5.S3.Combinatorics.GroupWords.InvolutionExactLength

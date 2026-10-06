/- GID: D5/S3/Combinatorics/MetallicHankel/MetallicHankelPeriod
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MetallicHankel/MetallicHankelPeriod
   mirror-E: none(waiver:periodic-orthogonality-hankel-propagation)
   anchors: [mathlib/module/Mathlib.Algebra.Ring.Parity]
   utility: none
   digest: Periodic monic moment relations propagate Hankel signs and bounds to every size. -/

import Mathlib.Algebra.Ring.Parity
import D5.S3.Combinatorics.MetallicHankel.MetallicHankelDeterminants

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MetallicHankel.MetallicHankelPeriod

open Finset MetallicHankelDefs MetallicHankelDeterminants

/-- A periodic monic approximation package controls every determinant size, including gaps. -/
theorem propagate (Φ : PowerSeries ℤ) (ℓ n L P : ℕ) (s k : ℕ → ℕ)
    (c : ℕ → ℕ → ℤ) (h : ℕ → ℤ)
    (s0 : s 0 = 0) (snext : ∀ p, s (p + 1) = s p + k p + 1)
    (sp : ∀ p, s (p + L) = s p + P)
    (kp : ∀ p, k (p + L) = k p) (hp : ∀ p, h (p + L) = h p)
    (cp : ∀ p, c (p + L) 0 = c p 0) (peven : Even P)
    (hsign : ∀ p, h p ∈ ({-1, 1} : Finset ℤ))
    (cvalues : ∀ p, c p 0 ∈ ({-1, 0, 1, 2} : Finset ℤ))
    (monic : ∀ p, c p (s p) = 1)
    (zeros : ∀ p t, t < s (p + 1) - 1 →
      ∑ r ∈ range (s p + 1), c p r * PowerSeries.coeff (ℓ + r + t) Φ = 0)
    (first : ∀ p, ∑ r ∈ range (s p + 1),
      c p r * PowerSeries.coeff (ℓ + r + (s (p + 1) - 1)) Φ = h p)
    (block : ∀ p, (∏ i ∈ range L,
      ((-1 : ℤ) ^ (k (p + i) * (k (p + i) + 1) / 2) *
        h (p + i) ^ (k (p + i) + 1))) = (-1 : ℤ) ^ n) :
    ∀ j, shiftedHankel Φ (ℓ + 1) (j + P) =
      (-1 : ℤ) ^ n * shiftedHankel Φ (ℓ + 1) j ∧
      shiftedHankel Φ (ℓ + 1) j ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
  classical
  let A : ℕ → ℤ := fun p => shiftedHankel Φ ℓ (s p)
  let C : ℕ → ℤ := fun p => shiftedHankel Φ (ℓ + 1) (s p)
  let w : ℕ → ℤ := fun p =>
    (-1 : ℤ) ^ (k p * (k p + 1) / 2) * h p ^ (k p + 1)
  have normal (p : ℕ) : A (p + 1) = w p * A p ∧
      C p = (-1 : ℤ) ^ (s p) * A p * c p 0 := by
    have z := zero_run Φ ℓ (s p) (k p + 1) (c p) (h p)
      (by omega) (monic p)
      (fun t ht => zeros p t (by rw [snext]; omega)) (by
        simpa only [snext, Nat.add_sub_cancel, Nat.add_assoc] using first p)
    constructor
    · simpa only [A, w, snext, Nat.add_assoc, Nat.add_sub_cancel, Nat.mul_comm] using z.1
    · exact z.2.2
  have product (p d : ℕ) : A (p + d) = (∏ i ∈ range d, w (p + i)) * A p := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [show p + (d + 1) = p + d + 1 by omega, (normal (p + d)).1, ih,
        prod_range_succ]
      ring
  have aperiod (p : ℕ) : A (p + L) = (-1 : ℤ) ^ n * A p := by
    rw [product, show (∏ i ∈ range L, w (p + i)) = (-1 : ℤ) ^ n from block p]
  have cperiod (p : ℕ) : C (p + L) = (-1 : ℤ) ^ n * C p := by
    rw [(normal (p + L)).2, (normal p).2, sp, aperiod, cp, pow_add,
      peven.neg_one_pow, mul_one]
    ring
  have sign_power (x : ℤ) (hx : x = 1 ∨ x = -1) (d : ℕ) :
      x ^ d = 1 ∨ x ^ d = -1 := by
    rcases hx with rfl | rfl
    · simp
    · exact neg_one_pow_eq_or ℤ d
  have sign_mul (x y : ℤ) (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
      x * y = 1 ∨ x * y = -1 := by
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num
  have hunit (p : ℕ) : h p = 1 ∨ h p = -1 := by
    have hz := hsign p
    simp only [mem_insert, mem_singleton] at hz
    exact hz.symm
  have aunit : ∀ p, A p = 1 ∨ A p = -1 := by
    intro p
    induction p with
    | zero =>
      left
      change shiftedHankel Φ ℓ (s 0) = 1
      rw [s0]
      exact Matrix.det_fin_zero
    | succ p ih =>
      rw [(normal p).1]
      apply sign_mul _ _ _ ih
      exact sign_mul _ _ (neg_one_pow_eq_or ℤ _) (sign_power _ (hunit p) _)
  have bounded_mul (x y : ℤ) (hx : x = 1 ∨ x = -1)
      (hy : y ∈ ({-2, -1, 0, 1, 2} : Finset ℤ)) :
      x * y ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
    simp only [mem_insert, mem_singleton] at hy ⊢
    rcases hx with rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have cbound (p : ℕ) : C p ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
    rw [(normal p).2]
    have hc : c p 0 ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
      have ht := cvalues p
      simp only [mem_insert, mem_singleton] at ht ⊢
      rcases ht with he | he | he | he <;> simp [he]
    exact bounded_mul _ _ (sign_mul _ _ (neg_one_pow_eq_or ℤ _) (aunit p)) hc
  have gap (p j : ℕ) (hj : s p ≤ j) (hnext : j < s (p + 1)) :
      shiftedHankel Φ (ℓ + 1) j =
        if j = s p then C p
        else if j = s p + k p then
          (-1 : ℤ) ^ (k p * (k p - 1) / 2) * h p ^ k p * C p else 0 := by
    by_cases he : j = s p
    · simp [he, C]
    · have hk : 0 < k p := by have hs := snext p; omega
      have shifted := zero_run Φ (ℓ + 1) (s p) (k p) (c p) (h p) hk (monic p)
        (by
          intro t ht
          have hz := zeros p (t + 1) (by rw [snext]; omega)
          convert hz using 1
          apply sum_congr rfl
          intro r _
          rw [show ℓ + 1 + r + t = ℓ + r + (t + 1) by omega])
        (by
          have hf := first p
          convert hf using 1
          apply sum_congr rfl
          intro r _
          rw [show ℓ + 1 + r + (s p + k p - 1) =
            ℓ + r + (s (p + 1) - 1) by rw [snext]; omega])
      by_cases hf : j = s p + k p
      · rw [if_neg he, if_pos hf]
        simpa only [hf, C] using shifted.1
      · simp only [he, if_false, hf]
        exact shifted.2.1 j (by omega) (by rw [snext] at hnext; omega)
  have cover : ∀ j, ∃ p, s p ≤ j ∧ j < s (p + 1) := by
    intro j
    induction j with
    | zero => exact ⟨0, by rw [s0], by rw [snext, s0]; omega⟩
    | succ j ih =>
      obtain ⟨p, hj, hn⟩ := ih
      by_cases hlt : j + 1 < s (p + 1)
      · exact ⟨p, by omega, hlt⟩
      · refine ⟨p + 1, by omega, ?_⟩
        rw [snext]
        omega
  intro j
  obtain ⟨p, hj, hn⟩ := cover j
  have newlo : s (p + L) ≤ j + P := by rw [sp]; omega
  have newhi : j + P < s (p + L + 1) := by
    rw [show p + L + 1 = (p + 1) + L by omega, sp]
    omega
  rw [gap p j hj hn, gap (p + L) (j + P) newlo newhi, sp, kp, hp, cperiod]
  have normaltest : j + P = s p + P ↔ j = s p := by omega
  have finaltest : j + P = s p + P + k p ↔ j = s p + k p := by omega
  rw [if_congr normaltest rfl rfl, if_congr finaltest rfl rfl]
  constructor
  · split_ifs <;> ring
  · split_ifs
    · exact cbound p
    · apply bounded_mul _ _ _ (cbound p)
      exact sign_mul _ _ (neg_one_pow_eq_or ℤ _) (sign_power _ (hunit p) _)
    · norm_num

end D5.S3.Combinatorics.MetallicHankel.MetallicHankelPeriod

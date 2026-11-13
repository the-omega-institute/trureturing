/- GID: D5/S3/Quantum/Dynamics/OddSquareGreenMass
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/OddSquareGreenMass
   mirror-E: none(waiver:pure-finite-matrix-estimate)
   anchors: []
   utility: none
   digest: Quadratic Green-entry mass from a repeated odd hopping block. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Odd repeated hopping blocks force a quadratic mass of zero-energy Green entries. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.OddSquareGreenMass

open Finset Matrix
open scoped BigOperators

/-- Absolute zero-energy Green entry from even site `2*l` to odd site `2*(l+d)+1`.
The recurrence is the forward substitution for the odd/even bidiagonal block. -/
def greenEntry (t : ℕ → ℝ) (l : ℕ) : ℕ → ℝ
  | 0 => 1 / t (2 * l)
  | d + 1 => greenEntry t l d * t (2 * (l + d) + 1) / t (2 * (l + d + 1))

theorem entry_pos (t : ℕ → ℝ) (ht : ∀ i, 0 < t i) (l d : ℕ) :
    0 < greenEntry t l d := by
  induction d with
  | zero => exact one_div_pos.mpr (ht _)
  | succ d ih => exact div_pos (mul_pos ih (ht _)) (ht _)

/-- The sign-conjugated odd/even block of an open weighted path. -/
def lowerBlock (t : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i : Fin n => t (2 * i.val)) -
    Matrix.of (fun i j : Fin n => if j.val + 1 = i.val then t (2 * j.val + 1) else 0)

def greenMatrix (t : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j.val ≤ i.val then greenEntry t j.val (i.val - j.val) else 0

theorem block_inverse (t : ℕ → ℝ) (ht : ∀ i, 0 < t i) (n : ℕ) :
    (lowerBlock t n)⁻¹ = greenMatrix t n := by
  apply Matrix.inv_eq_right_inv
  ext i j
  rw [lowerBlock, Matrix.sub_mul]
  rw [Matrix.sub_apply, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  by_cases hi : i.val = 0
  · have hs : (∑ k : Fin n,
        (if k.val + 1 = i.val then t (2 * k.val + 1) else 0) * greenMatrix t n k j) = 0 := by
      apply sum_eq_zero
      intro k _
      rw [ite_eq_right (by omega), zero_mul]
    rw [hs, sub_zero]
    by_cases hj : j = i
    · subst j
      simp [greenMatrix, greenEntry, ne_of_gt (ht _)]
    · have hjv : ¬j.val ≤ i.val := by
        intro h
        apply hj
        apply Fin.ext
        omega
      simp [greenMatrix, hjv, Matrix.one_apply_ne (Ne.symm hj)]
  · let k : Fin n := ⟨i.val - 1, by omega⟩
    have hk : k.val + 1 = i.val := by dsimp [k]; omega
    have hs : (∑ r : Fin n,
        (if r.val + 1 = i.val then t (2 * r.val + 1) else 0) * greenMatrix t n r j) =
        t (2 * k.val + 1) * greenMatrix t n k j := by
      rw [sum_eq_single k]
      · rw [ite_eq_left hk]
      · intro r _ hr
        have hh : r.val + 1 ≠ i.val := by
          intro h
          apply hr
          apply Fin.ext
          omega
        rw [ite_eq_right hh, zero_mul]
      · simp
    rw [hs]
    by_cases hj : j = i
    · subst j
      simp [greenMatrix, greenEntry, show ¬i.val ≤ k.val by omega,
        ne_of_gt (ht _)]
    · by_cases hji : j.val ≤ i.val
      · have hjk : j.val ≤ k.val := by
          have hne : j.val ≠ i.val := fun h => hj (Fin.ext h)
          omega
        have hd : i.val - j.val = (k.val - j.val) + 1 := by omega
        have he : j.val + (k.val - j.val) = k.val := by omega
        simp only [greenMatrix, ite_eq_left hji, ite_eq_left hjk, hd, greenEntry, he]
        rw [show k.val + 1 = i.val from hk]
        rw [Matrix.one_apply_ne (Ne.symm hj)]
        field_simp [ne_of_gt (ht (2 * i.val))]
        ring
      · have hjk : ¬j.val ≤ k.val := by omega
        simp [greenMatrix, hji, hjk, Matrix.one_apply_ne (Ne.symm hj)]

private theorem odd_shift_pair (t : ℕ → ℝ) (q : ℕ)
    (ht : ∀ i, 0 < t i)
    (hp : ∀ i < 2 * q, t (i + (2 * q + 1)) = t i)
    (l d : ℕ) (hld : l + d + 1 ≤ q) :
    greenEntry t l (d + 1) * greenEntry t (q + l + 1) d =
      1 / (t (2 * l) * t (2 * (l + d + 1))) := by
  induction d with
  | zero =>
    have h := hp (2 * l + 1) (by omega)
    have he : 2 * (q + l + 1) = (2 * l + 1) + (2 * q + 1) := by omega
    simp only [greenEntry, Nat.add_zero, he, h]
    field_simp [ne_of_gt (ht (2 * l + 1))]
  | succ d ih =>
    have hi := ih (by omega)
    have h₁ := hp (2 * (l + d + 1)) (by omega)
    have h₂ := hp (2 * (l + d + 1) + 1) (by omega)
    have he₁ : 2 * (q + l + 1 + d) + 1 =
        2 * (l + d + 1) + (2 * q + 1) := by omega
    have he₂ : 2 * (q + l + 1 + d + 1) =
        (2 * (l + d + 1) + 1) + (2 * q + 1) := by omega
    change (greenEntry t l (d + 1) * t (2 * (l + (d + 1)) + 1) /
        t (2 * (l + (d + 1) + 1))) *
        (greenEntry t (q + l + 1) d * t (2 * (q + l + 1 + d) + 1) /
        t (2 * (q + l + 1 + d + 1))) = _
    rw [he₁, he₂, h₁, h₂]
    simp only [← Nat.add_assoc] at hi ⊢
    have hn (i : ℕ) : t i ≠ 0 := ne_of_gt (ht i)
    calc
      _ = (greenEntry t l (d + 1) * greenEntry t (q + l + 1) d) *
          t (2 * (l + d + 1)) / t (2 * (l + d + 1 + 1)) := by
        field_simp [hn]
      _ = _ := by rw [hi]; field_simp [hn]

/-- The two triangular parts inside a doubled block of odd length `2*q+1`
have quadratic total Green mass. Only the actual repeated bonds are assumed. -/
private theorem odd_square_paired_mass (t : ℕ → ℝ) (q : ℕ)
    (ht : ∀ i, 0 < t i) (hu : ∀ i, t i ≤ 1)
    (hp : ∀ i < 2 * q, t (i + (2 * q + 1)) = t i) :
    (q : ℝ) * (q + 1) ≤
      ∑ l ∈ range q, ∑ d ∈ range (q - l),
        (greenEntry t l (d + 1) + greenEntry t (q + l + 1) d) := by
  have hpair (l d : ℕ) (hl : l < q) (hd : d < q - l) :
      (2 : ℝ) ≤ greenEntry t l (d + 1) + greenEntry t (q + l + 1) d := by
    have he := odd_shift_pair t q ht hp l d (by omega)
    have hprod : t (2 * l) * t (2 * (l + d + 1)) ≤ 1 := by
      nlinarith [ht (2 * l), ht (2 * (l + d + 1)),
        hu (2 * l), hu (2 * (l + d + 1))]
    have hge : 1 ≤ greenEntry t l (d + 1) * greenEntry t (q + l + 1) d := by
      rw [he]
      exact (le_div_iff₀ (mul_pos (ht _) (ht _))).mpr (by simpa using hprod)
    have hpos₁ := entry_pos t ht l (d + 1)
    have hpos₂ := entry_pos t ht (q + l + 1) d
    nlinarith [sq_nonneg (greenEntry t l (d + 1) - greenEntry t (q + l + 1) d)]
  have hsum : (q : ℝ) * (q + 1) =
      ∑ l ∈ range q, ∑ _d ∈ range (q - l), (2 : ℝ) := by
    clear hp hpair
    induction q with
    | zero => simp
    | succ q ih =>
      rw [sum_range_succ']
      simp only [Nat.sub_zero, sum_const, card_range, nsmul_eq_mul]
      have hs : (∑ l ∈ range q, (↑(q + 1 - (l + 1)) : ℝ) * 2) =
          ∑ l ∈ range q, ∑ _d ∈ range (q - l), (2 : ℝ) := by
        apply sum_congr rfl
        intro l hl
        simp [show q + 1 - (l + 1) = q - l by omega]
      rw [hs, ← ih]
      push_cast
      ring
  rw [hsum]
  apply sum_le_sum
  intro l hl
  apply sum_le_sum
  intro d hd
  exact hpair l d (mem_range.mp hl) (mem_range.mp hd)

/-- A repeated odd block forces quadratic mass in two triangular regions of the actual
inverse bidiagonal matrix. The finite indices include both endpoints of every region. -/
theorem odd_square_inverse_paired_mass (t : ℕ → ℝ) (q : ℕ)
    (ht : ∀ i, 0 < t i) (hu : ∀ i, t i ≤ 1)
    (hp : ∀ i < 2 * q, t (i + (2 * q + 1)) = t i) :
    (q : ℝ) * (q + 1) ≤
      ∑ l : Fin q, ∑ d : Fin (q - l.val),
        ((lowerBlock t (2 * q + 1))⁻¹
          ⟨l.val + d.val + 1, by have := l.isLt; have := d.isLt; omega⟩
          ⟨l.val, by have := l.isLt; omega⟩ +
        (lowerBlock t (2 * q + 1))⁻¹
          ⟨q + l.val + d.val + 1, by have := l.isLt; have := d.isLt; omega⟩
          ⟨q + l.val + 1, by have := l.isLt; omega⟩) := by
  rw [block_inverse t ht]
  have he (l : Fin q) (d : Fin (q - l.val)) :
      greenMatrix t (2 * q + 1)
        ⟨l.val + d.val + 1, by have := l.isLt; have := d.isLt; omega⟩
        ⟨l.val, by have := l.isLt; omega⟩ +
      greenMatrix t (2 * q + 1)
        ⟨q + l.val + d.val + 1, by have := l.isLt; have := d.isLt; omega⟩
        ⟨q + l.val + 1, by have := l.isLt; omega⟩ =
        greenEntry t l.val (d.val + 1) + greenEntry t (q + l.val + 1) d.val := by
    simp only [greenMatrix]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    congr 2 <;> omega
  simp_rw [he]
  have hs (l : Fin q) :
      (∑ d : Fin (q - l.val),
        (greenEntry t l.val (d.val + 1) + greenEntry t (q + l.val + 1) d.val)) =
      ∑ d ∈ range (q - l.val),
        (greenEntry t l.val (d + 1) + greenEntry t (q + l.val + 1) d) :=
    Fin.sum_univ_eq_sum_range
      (fun d : ℕ => greenEntry t l.val (d + 1) + greenEntry t (q + l.val + 1) d)
      (q - l.val)
  simp_rw [hs]
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => (∑ d ∈ range (q - l),
    (greenEntry t l (d + 1) + greenEntry t (q + l + 1) d))) q]
  exact odd_square_paired_mass t q ht hu hp

end D5.S3.Quantum.Dynamics.OddSquareGreenMass

#print axioms D5.S3.Quantum.Dynamics.OddSquareGreenMass.odd_square_inverse_paired_mass

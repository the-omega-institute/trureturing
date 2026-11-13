/- GID: D5/S3/Quantum/Dynamics/OddSquareFullInverseNorm
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/OddSquareFullInverseNorm
   mirror-E: none(waiver:pure-finite-matrix-estimate)
   anchors: []
   utility: none
   digest: Euclidean amplification in the full inverse from an interior odd repeated block. -/

import D5.S3.Quantum.Dynamics.OddSquareGreenMass
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Full Euclidean inverse amplification from a repeated odd interior window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.OddSquareFullInverseNorm

open Finset Matrix WithLp
open OddSquareGreenMass
open scoped BigOperators

private theorem green_shift (t : ℕ → ℝ) (a l d : ℕ) :
    greenEntry (fun i => t (2 * a + i)) l d = greenEntry t (a + l) d := by
  induction d with
  | zero => simp [greenEntry, Nat.mul_add]
  | succ d ih =>
    simp only [greenEntry, ih]
    rw [show 2 * a + (2 * (l + d) + 1) = 2 * (a + l + d) + 1 by omega,
      show 2 * a + 2 * (l + d + 1) = 2 * (a + l + d + 1) by omega]

private theorem inverse_shift (t : ℕ → ℝ) (ht : ∀ i, 0 < t i)
    (a m n : ℕ) (hm : a + m ≤ n) (i j : Fin m) :
    (lowerBlock t n)⁻¹
      ⟨a + i.val, by have := i.isLt; omega⟩
      ⟨a + j.val, by have := j.isLt; omega⟩ =
    (lowerBlock (fun k => t (2 * a + k)) m)⁻¹ i j := by
  rw [block_inverse t ht, block_inverse _ (fun k => ht _)]
  simp only [greenMatrix, Nat.add_le_add_iff_left, Nat.add_sub_add_left]
  split_ifs
  · exact (green_shift t a j.val (i.val - j.val)).symm
  · rfl

private theorem sum_injective_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (f : β → ℝ) (hf : ∀ i, 0 ≤ f i)
    (e : α → β) (he : Function.Injective e) :
    (∑ i, f (e i)) ≤ ∑ j, f j := by
  classical
  apply Finset.sum_le_sum_of_injOn e (he.injOn) (by simp)
  · intro i hi; rfl
  · intro j hj hje; exact hf j

/-- An odd repeated window inside the actual finite path amplifies a unit Euclidean vector.
The inverse is that of the whole bidiagonal block, including both exterior parts. -/
theorem full_inverse_unit_amplification (t : ℕ → ℝ) (n a q : ℕ)
    (ht : ∀ i, 0 < t i) (hu : ∀ i, t i ≤ 1)
    (hq : 1 ≤ q) (hwindow : a + (2 * q + 1) ≤ n)
    (hp : ∀ i < 2 * q,
      t (2 * a + (i + (2 * q + 1))) = t (2 * a + i)) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧
      (q : ℝ) * (q + 1) ≤
        2 * (n : ℝ) * ‖Matrix.toEuclideanLin ((lowerBlock t n)⁻¹) v‖ := by
  classical
  let G := (lowerBlock t n)⁻¹
  have hG (i j : Fin n) : 0 ≤ G i j := by
    dsimp [G]
    rw [block_inverse t ht]
    simp only [greenMatrix]
    split_ifs
    · exact (entry_pos t ht _ _).le
    · exact le_rfl
  let c₁ : Fin q → Fin n := fun l => ⟨a + l.val, by have := l.isLt; omega⟩
  let c₂ : Fin q → Fin n := fun l => ⟨a + (q + l.val + 1), by have := l.isLt; omega⟩
  let r₁ (l : Fin q) : Fin (q - l.val) → Fin n :=
    fun d => ⟨a + (l.val + d.val + 1), by have := d.isLt; have := l.isLt; omega⟩
  let r₂ (l : Fin q) : Fin (q - l.val) → Fin n :=
    fun d => ⟨a + (q + l.val + d.val + 1), by have := d.isLt; have := l.isLt; omega⟩
  have hm := odd_square_inverse_paired_mass (fun k => t (2 * a + k)) q
    (fun k => ht _) (fun k => hu _) hp
  have he (l : Fin q) (d : Fin (q - l.val)) :
      (lowerBlock (fun k => t (2 * a + k)) (2 * q + 1))⁻¹
          ⟨l.val + d.val + 1, by have := l.isLt; have := d.isLt; omega⟩
          ⟨l.val, by have := l.isLt; omega⟩ +
        (lowerBlock (fun k => t (2 * a + k)) (2 * q + 1))⁻¹
          ⟨q + l.val + d.val + 1, by have := l.isLt; have := d.isLt; omega⟩
          ⟨q + l.val + 1, by have := l.isLt; omega⟩ =
        G (r₁ l d) (c₁ l) + G (r₂ l d) (c₂ l) := by
    rw [← inverse_shift t ht a (2 * q + 1) n hwindow,
      ← inverse_shift t ht a (2 * q + 1) n hwindow]
  simp_rw [he, Finset.sum_add_distrib] at hm
  have hregion (c : Fin q → Fin n) (hc : Function.Injective c)
      (r : (l : Fin q) → Fin (q - l.val) → Fin n)
      (hr : ∀ l, Function.Injective (r l)) :
      (∑ l, ∑ d, G (r l d) (c l)) ≤ ∑ j, ∑ i, G i j := by
    calc
      _ ≤ ∑ l, ∑ i, G i (c l) := by
        apply sum_le_sum
        intro l hl
        exact sum_injective_nonneg (fun i => G i (c l)) (fun i => hG i _) (r l) (hr l)
      _ ≤ _ := sum_injective_nonneg (fun j => ∑ i, G i j)
        (fun j => sum_nonneg (fun i hi => hG i j)) c hc
  have hc₁ : Function.Injective c₁ := by
    intro l k h; apply Fin.ext; have := congrArg Fin.val h; dsimp [c₁] at this; omega
  have hc₂ : Function.Injective c₂ := by
    intro l k h; apply Fin.ext; have := congrArg Fin.val h; dsimp [c₂] at this; omega
  have hr₁ (l : Fin q) : Function.Injective (r₁ l) := by
    intro d e h; apply Fin.ext; have := congrArg Fin.val h; dsimp [r₁] at this; omega
  have hr₂ (l : Fin q) : Function.Injective (r₂ l) := by
    intro d e h; apply Fin.ext; have := congrArg Fin.val h; dsimp [r₂] at this; omega
  have hmass : (q : ℝ) * (q + 1) ≤ 2 * (∑ j, ∑ i, G i j) := by
    have h₁ := hregion c₁ hc₁ r₁ hr₁
    have h₂ := hregion c₂ hc₂ r₂ hr₂
    linarith
  let x : EuclideanSpace ℝ (Fin n) := toLp 2 (fun _ => 1)
  let A := Matrix.toEuclideanLin G
  have hx : ‖x‖ ^ 2 = (n : ℝ) := by
    simp [EuclideanSpace.real_norm_sq_eq, x]
  have hn : 0 < n := by omega
  have hxpos : 0 < ‖x‖ := by
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    nlinarith [norm_nonneg x]
  let v : EuclideanSpace ℝ (Fin n) := ‖x‖⁻¹ • x
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, hxpos.ne']
  refine ⟨v, hv, ?_⟩
  have hinner : (∑ j, ∑ i, G i j) = inner ℝ x (A x) := by
    rw [Finset.sum_comm]
    simp [x, A, Matrix.toLpLin_apply, PiLp.inner_apply, Matrix.mulVec, dotProduct]
  have hcs := real_inner_le_norm x (A x)
  have hxv : x = ‖x‖ • v := by
    simp [v, smul_smul, hxpos.ne']
  have hAx : ‖A x‖ = ‖x‖ * ‖A v‖ := by
    conv_lhs => rw [hxv, map_smul]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hxpos]
  rw [hAx] at hcs
  rw [← mul_assoc, ← pow_two, hx] at hcs
  rw [hinner] at hmass
  calc
    _ ≤ 2 * inner ℝ x (A x) := hmass
    _ ≤ 2 * ((n : ℝ) * ‖A v‖) := mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ = _ := by ring

end D5.S3.Quantum.Dynamics.OddSquareFullInverseNorm

#print axioms D5.S3.Quantum.Dynamics.OddSquareFullInverseNorm.full_inverse_unit_amplification

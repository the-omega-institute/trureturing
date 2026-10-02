/- GID: D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.claim; result=D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.result; claim=D5/S3/StatisticalMechanics/PaddedGinibreNonHalfIntegerRefutation.claim
   digest: The PGG inequalities fail for a stable determinant at exponent eta = 1/4. -/

/-
proof_shape: P: definition (determinantal polynomial)
proof_shape: evenIndex: definition (parity predicate)
proof_shape: pggSum: definition (PGG sum, using Matrix.vecMul)
proof_shape: claim: definition (published positive-exponent assertion)
proof_shape: result: bind-only (explicit finite evaluation and fourth-power comparisons,
  using pinned Mathlib positivity and real-power identities)
escape_witness: none
admission_basis: open-problem-resolution (#11488; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation

open Matrix Finset

/-- The determinantal polynomial in the setting of Theorem 2.3, arXiv:2207.07603v2, p. 9. -/
noncomputable def P {n q : ℕ} (A : Fin n → Matrix (Fin q) (Fin q) ℝ)
    (x : Fin n → ℝ) : ℝ := (∑ j, x j • A j).det

/-- A natural multi-index is even when its integer cast lies in the kernel of the parity
homomorphism (arXiv:2207.07603v2, p. 5). -/
def evenIndex {n L : ℕ} (ρ : (Fin n → ℤ) →+ (Fin L → ZMod 2))
    (a : Fin n → ℕ) : Prop := ρ (fun j => (a j : ℤ)) = 0

/-- The PGG sum of Theorem 2.3 with exponent `η`. The binary vector `α` indexes each pair
`α + β = 1` exactly once, with `β_i = 1 - α_i`. -/
noncomputable def pggSum {n q L m : ℕ}
    (A : Fin n → Matrix (Fin q) (Fin q) ℝ)
    (ρ : (Fin n → ℤ) →+ (Fin L → ZMod 2)) (V : Fin m → Fin n → ℕ)
    (ε : Fin m → ℤ) (u : Fin n → ℕ) (η : ℝ) : ℝ := by
  classical
  exact ∑ α : Fin m → Fin 2,
    (if evenIndex ρ (Matrix.vecMul (fun i => (α i).val) V) then 1 else 0 : ℝ) *
    (∏ i, (ε i : ℝ) ^ (1 - (α i).val)) *
    (P A (fun j => ((u j + Matrix.vecMul (fun i => (α i).val) V j : ℕ) : ℝ))) ^ (-η) *
    (P A (fun j => ((u j + Matrix.vecMul (fun i => 1 - (α i).val) V j : ℕ) : ℝ))) ^ (-η)

/-- Problem 3 asks whether all the PGG inequalities of Theorem 2.3 remain valid for every
positive real exponent, with the same matrix, parity, sign and padding hypotheses. -/
def claim : Prop :=
  ∀ η : ℝ, 0 < η → ∀ (n q L : ℕ) (A : Fin n → Matrix (Fin q) (Fin q) ℝ)
    (ρ : (Fin n → ℤ) →+ (Fin L → ZMod 2)),
    0 < q → (∀ j, (A j).PosSemidef) → (∑ j, A j).PosDef →
    ∀ (m : ℕ) (V : Fin m → Fin n → ℕ) (ε : Fin m → ℤ) (u : Fin n → ℕ),
      evenIndex ρ (Matrix.vecMul (fun _ => 1) V) → (∀ i, ε i = 1 ∨ ε i = -1) →
      (∀ j, 0 < u j) → evenIndex ρ u → 0 ≤ pggSum A ρ V ε u η

/-- Problem 3 has a negative answer: exponent `1/4` already fails for three real positive
semidefinite `2 × 2` matrices, trivial parity, and four rows. -/
theorem result : ¬ claim := by
  classical
  let A : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ :=
    ![!![1, 0; 0, 0], !![0, 0; 0, 1], !![1, 1; 1, 1]]
  let V : Fin 4 → Fin 3 → ℕ := ![![1, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]
  let ρ : (Fin 3 → ℤ) →+ (Fin 0 → ZMod 2) := 0
  have hA : ∀ j, (A j).PosSemidef := by
    intro j
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · ext i k
      fin_cases j <;> fin_cases i <;> fin_cases k <;> norm_num [A, Matrix.IsHermitian,
        Matrix.conjTranspose_apply]
    · intro x
      fin_cases j
      · simpa [A, dotProduct, Matrix.mulVec, Fin.sum_univ_two] using mul_self_nonneg (x 0)
      · simpa [A, dotProduct, Matrix.mulVec, Fin.sum_univ_two] using mul_self_nonneg (x 1)
      · change 0 ≤ star x ⬝ᵥ (A 2 *ᵥ x)
        have hform : star x ⬝ᵥ (A 2 *ᵥ x) = (x 0 + x 1) ^ 2 := by
          simp [A, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_two,
            Matrix.vecHead, Matrix.vecTail]
          ring
        rw [hform]
        exact sq_nonneg _
  have hsum : (∑ j, A j).PosDef := by
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    constructor
    · ext i k
      fin_cases i <;> fin_cases k <;> norm_num [A, Matrix.IsHermitian,
        Matrix.conjTranspose_apply, Fin.sum_univ_three] <;> rfl
    · intro x hx
      have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra hn
        push Not at hn
        apply hx
        ext i
        fin_cases i <;> simp [hn.1, hn.2]
      have hform : star x ⬝ᵥ ((∑ j, A j) *ᵥ x) =
          (x 0) ^ 2 + (x 1) ^ 2 + (x 0 + x 1) ^ 2 := by
        simp [A, dotProduct, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_two,
          Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
        ring
      rw [hform]
      rcases hn with h0 | h1
      · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (x 1), sq_nonneg (x 0 + x 1)]
      · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (x 0), sq_nonneg (x 0 + x 1)]
  have hpoly (x : Fin 3 → ℝ) : P A x = x 0 * x 1 + x 0 * x 2 + x 1 * x 2 := by
    simp [P, A, Fin.sum_univ_three, Matrix.det_fin_two]
    ring
  have huniv : (univ : Finset (Fin 4 → Fin 2)) =
      {![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1],
       ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 1, 1, 1],
       ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0], ![1, 0, 1, 1],
       ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 0], ![1, 1, 1, 1]} := by decide
  have heval : pggSum A ρ V (fun _ => -1) (fun _ => 1) (1 / 4) =
      2 * (48 : ℝ) ^ (-1 / 4 : ℝ) - 4 * (55 : ℝ) ^ (-1 / 4 : ℝ) +
      2 * (56 : ℝ) ^ (-1 / 4 : ℝ) - 4 * (60 : ℝ) ^ (-1 / 4 : ℝ) +
      4 * (64 : ℝ) ^ (-1 / 4 : ℝ) := by
    unfold pggSum
    rw [huniv]
    norm_num [evenIndex, ρ, Matrix.vecMul, dotProduct, V, hpoly, Fin.sum_univ_four, Fin.prod_univ_four, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
    rw [← show (16 : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / 2 by norm_num]
    have hm (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
        x ^ (-(1 / 4 : ℝ)) * y ^ (-(1 / 4 : ℝ)) = (x * y) ^ (-(1 / 4 : ℝ)) :=
      (Real.mul_rpow hx hy).symm
    rw [hm 3 16 (by norm_num) (by norm_num), hm 16 3 (by norm_num) (by norm_num),
      hm 5 11 (by norm_num) (by norm_num), hm 11 5 (by norm_num) (by norm_num),
      hm 8 7 (by norm_num) (by norm_num), hm 7 8 (by norm_num) (by norm_num),
      hm 5 12 (by norm_num) (by norm_num), hm 12 5 (by norm_num) (by norm_num),
      hm 8 8 (by norm_num) (by norm_num)]
    norm_num
    ring
  have hupper (p k : ℝ) (hp : 0 < p) (hk : 0 ≤ k) (hc : 1 < p * k ^ 4) :
      p ^ (-1 / 4 : ℝ) < k := by
    apply (Real.rpow_lt_rpow_iff (Real.rpow_nonneg hp.le _) hk (by norm_num : (0 : ℝ) < 4)).mp
    rw [← Real.rpow_mul hp.le, show (-1 / 4 : ℝ) * 4 = -1 by norm_num,
      Real.rpow_neg_one, Real.rpow_ofNat]
    exact (inv_lt_iff_one_lt_mul₀' hp).mpr hc
  have hlower (p k : ℝ) (hp : 0 < p) (hk : 0 ≤ k) (hc : p * k ^ 4 < 1) :
      k < p ^ (-1 / 4 : ℝ) := by
    apply (Real.rpow_lt_rpow_iff hk (Real.rpow_nonneg hp.le _) (by norm_num : (0 : ℝ) < 4)).mp
    rw [← Real.rpow_mul hp.le, show (-1 / 4 : ℝ) * 4 = -1 by norm_num,
      Real.rpow_neg_one, Real.rpow_ofNat]
    simpa only [mul_one] using (lt_inv_mul_iff₀ hp).mpr hc
  have h48 := hupper 48 (3800 / 10000) (by norm_num) (by norm_num) (by norm_num)
  have h56 := hupper 56 (3656 / 10000) (by norm_num) (by norm_num) (by norm_num)
  have h64 := hupper 64 (3536 / 10000) (by norm_num) (by norm_num) (by norm_num)
  have h55 := hlower 55 (3672 / 10000) (by norm_num) (by norm_num) (by norm_num)
  have h60 := hlower 60 (3593 / 10000) (by norm_num) (by norm_num) (by norm_num)
  intro h
  have hnonneg := h (1 / 4) (by norm_num) 3 2 0 A ρ (by norm_num) hA hsum 4 V
    (fun _ => -1) (fun _ => 1) (by simp [evenIndex, ρ]) (by simp) (by simp)
    (by simp [evenIndex, ρ])
  rw [heval] at hnonneg
  linarith

end D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation

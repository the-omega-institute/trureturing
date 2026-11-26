/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/RectangularAlternating
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Balancing opposite spectral weights for a rectangular alternating trace. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.AlternatingMidpoint

/-! Geometric midpoints of opposite diagonal factors lower the real
four-copy trace for a rectangular coupling with an affine binary block. -/

namespace RefinedBMV.Tracial

open Matrix
open scoped BigOperators

open private realDiagonal trace_realDiagonal_pair from
  D5.S3.Quantum.Analysis.RefinedBMV.Tracial.AlternatingMidpoint

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Symmetric nonnegative off-diagonal trace weights allow geometric
balancing of the two diagonal factors. The diagonal weights cancel. -/
theorem alternating_midpoint_of_pair_weights (a c : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i) (Y Z : Matrix ι ι ℂ)
    (hsym : ∀ i j, (Y i j * Z j i).re = (Y j i * Z i j).re)
    (hpos : ∀ i j, i ≠ j → 0 ≤ (Y i j * Z j i).re) :
    let D := realDiagonal (fun i ↦ Real.sqrt (a i * c i))
    (trace ((D * Y) * (D * Z))).re ≤
      (trace ((realDiagonal a * Y) * (realDiagonal c * Z))).re := by
  dsimp only
  rw [trace_realDiagonal_pair, trace_realDiagonal_pair]
  let w (i j : ι) := (Y i j * Z j i).re
  have hswap (i j : ι) :
      Real.sqrt (a i * c i) * Real.sqrt (a j * c j) =
        Real.sqrt (a i * c j) * Real.sqrt (a j * c i) := by
    rw [← Real.sqrt_mul (mul_nonneg (ha i) (hc i)),
      ← Real.sqrt_mul (mul_nonneg (ha i) (hc j))]
    congr 1
    ring
  have hsum : (∑ i, ∑ j, a j * c i * w i j) = ∑ i, ∑ j, a i * c j * w i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      rw [show w j i = w i j from hsym j i]
  change (∑ i, ∑ j, Real.sqrt (a i * c i) * Real.sqrt (a j * c j) * w i j) ≤ _
  calc
    _ ≤ ∑ i, ∑ j, ((a i * c j + a j * c i) / 2) * w i j := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases h : i = j
      · subst j
        rw [← pow_two, Real.sq_sqrt (mul_nonneg (ha i) (hc i))]
        exact le_of_eq (by ring)
      have hp := Real.sq_sqrt (mul_nonneg (ha i) (hc j))
      have hq := Real.sq_sqrt (mul_nonneg (ha j) (hc i))
      have hamgm : Real.sqrt (a i * c j) * Real.sqrt (a j * c i) ≤
          (a i * c j + a j * c i) / 2 := by
        nlinarith only [hp, hq, sq_nonneg (Real.sqrt (a i * c j) - Real.sqrt (a j * c i))]
      rw [hswap]
      exact mul_le_mul_of_nonneg_right hamgm (hpos i j h)
    _ = ∑ i, ∑ j, a i * c j * w i j := by
      simp_rw [show ∀ i j, ((a i * c j + a j * c i) / 2) * w i j =
        (a i * c j * w i j + a j * c i * w i j) / 2 by intro i j; ring]
      simp only [← Finset.sum_div, Finset.sum_add_distrib, hsum]
      ring

omit [Fintype ι] in
private theorem affine_pair_weight_off (g : ι → ℝ) {J : Matrix ι ι ℂ}
    (hJ : J.IsHermitian) (u v r t : ℝ) {i j : ι} (hij : i ≠ j) :
    ((((u : ℂ) • realDiagonal g + (r : ℂ) • J) i j) *
      (((v : ℂ) • realDiagonal g + (t : ℂ) • J) j i)).re =
        r * t * Complex.normSq (J i j) := by
  simp only [Matrix.add_apply, Matrix.smul_apply, realDiagonal, Matrix.diagonal_apply,
    ite_eq_right hij, ite_eq_right (Ne.symm hij), smul_eq_mul, mul_zero, zero_add]
  have hconj : J j i = star (J i j) := (hJ.apply j i).symm
  rw [hconj]
  calc
    _ = (((r * t : ℝ) : ℂ) * (star (J i j) * J i j)).re := by
      congr 1
      push_cast
      ring
    _ = _ := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul,
        Complex.ofReal_re]

private theorem alternating_diagonal_affine_midpoint_le (a c g : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i) {J : Matrix ι ι ℂ} (hJ : J.IsHermitian)
    (u v r t : ℝ) (hrt : 0 ≤ r * t) :
    let Y := (u : ℂ) • realDiagonal g + (r : ℂ) • J
    let Z := (v : ℂ) • realDiagonal g + (t : ℂ) • J
    let D := realDiagonal (fun i ↦ Real.sqrt (a i * c i))
    (trace ((D * Y) * (D * Z))).re ≤
      (trace ((realDiagonal a * Y) * (realDiagonal c * Z))).re := by
  dsimp only
  apply alternating_midpoint_of_pair_weights a c ha hc
  · intro i j
    by_cases h : i = j
    · subst j
      rfl
    rw [affine_pair_weight_off g hJ u v r t h, affine_pair_weight_off g hJ u v r t (Ne.symm h),
      ← hJ.apply i j, Complex.star_def, Complex.normSq_conj]
  · intro i j h
    rw [affine_pair_weight_off g hJ u v r t h]
    exact mul_nonneg hrt (Complex.normSq_nonneg _)

/-- The real trace of a four-slot product with a rectangular coupling. -/
def rectangularAlternatingTrace (X : Matrix ι κ ℂ) (A C : Matrix ι ι ℂ)
    (B D : Matrix κ κ ℂ) : ℝ :=
  (trace ((A * (X * B * Xᴴ)) * (C * (X * D * Xᴴ)))).re

omit [DecidableEq ι] [DecidableEq κ] in
private theorem rectangularTrace_rotate (X : Matrix ι κ ℂ) (A : Matrix ι ι ℂ)
    (B D : Matrix κ κ ℂ) :
    rectangularAlternatingTrace X A A B D =
      (trace ((B * (Xᴴ * A * X)) * (D * (Xᴴ * A * X)))).re := by
  let K := B * Xᴴ * A * X * D * Xᴴ
  calc
    rectangularAlternatingTrace X A A B D = (trace ((A * X) * K)).re := by
      simp only [rectangularAlternatingTrace, K, Matrix.mul_assoc]
    _ = (trace (K * (A * X))).re := congrArg Complex.re (trace_mul_comm (A * X) K)
    _ = _ := by simp only [K, Matrix.mul_assoc]

/-- Balance both pairs of opposite diagonal weights in a rectangular trace.
The top basis diagonalizes the Gram matrix. The two bottom weights lie in a
common affine span, as happens for exponentials of a binary spectrum. -/
theorem rectangular_alternating_midpoint_le
    (X : Matrix ι κ ℂ) (a c g : ι → ℝ) (b d : κ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i)
    (hb : ∀ i, 0 ≤ b i) (hd : ∀ i, 0 ≤ d i)
    (hGram : X * Xᴴ = realDiagonal g)
    {P : Matrix κ κ ℂ} (hP : P.IsHermitian) (u v r t : ℝ) (hrt : 0 ≤ r * t)
    (hB : realDiagonal b = (u : ℂ) • (1 : Matrix κ κ ℂ) + (r : ℂ) • P)
    (hD : realDiagonal d = (v : ℂ) • (1 : Matrix κ κ ℂ) + (t : ℂ) • P) :
    let A := realDiagonal (fun i ↦ Real.sqrt (a i * c i))
    let B := realDiagonal (fun i ↦ Real.sqrt (b i * d i))
    rectangularAlternatingTrace X A A B B ≤
      rectangularAlternatingTrace X (realDiagonal a) (realDiagonal c)
        (realDiagonal b) (realDiagonal d) := by
  dsimp only
  let A := realDiagonal (fun i ↦ Real.sqrt (a i * c i))
  let B := realDiagonal (fun i ↦ Real.sqrt (b i * d i))
  let J := X * P * Xᴴ
  let M := Xᴴ * A * X
  have hJ : J.IsHermitian := isHermitian_mul_mul_conjTranspose X hP
  have hA : A.IsHermitian := by
    change (diagonal fun i ↦ (Real.sqrt (a i * c i) : ℂ)).IsHermitian
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    simp [IsSelfAdjoint]
  have hM : M.IsHermitian := isHermitian_conjTranspose_mul_mul X hA
  have hB' : X * realDiagonal b * Xᴴ = (u : ℂ) • realDiagonal g + (r : ℂ) • J := by
    rw [hB, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_one, hGram]
  have hD' : X * realDiagonal d * Xᴴ = (v : ℂ) • realDiagonal g + (t : ℂ) • J := by
    rw [hD, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_one, hGram]
  calc
    rectangularAlternatingTrace X A A B B ≤
        rectangularAlternatingTrace X A A (realDiagonal b) (realDiagonal d) := by
      rw [rectangularTrace_rotate, rectangularTrace_rotate]
      apply alternating_midpoint_of_pair_weights b d hb hd
      · intro i j
        rw [mul_comm]
      · intro i j _
        change 0 ≤ (M i j * M j i).re
        rw [← hM.apply i j, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
          Complex.ofReal_re]
        exact Complex.normSq_nonneg _
    _ ≤ _ := by
      unfold rectangularAlternatingTrace
      rw [hB', hD']
      exact alternating_diagonal_affine_midpoint_le a c g ha hc hJ u v r t hrt

end RefinedBMV.Tracial

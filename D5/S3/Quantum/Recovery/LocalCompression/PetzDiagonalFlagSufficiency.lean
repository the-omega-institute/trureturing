/- GID: D5/S3/Quantum/Recovery/LocalCompression/PetzDiagonalFlagSufficiency
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/PetzDiagonalFlagSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sufficiency of stochastic merging for diagonal Petz recovery. -/

import D5.S3.Quantum.Recovery.LocalCompression.PetzDiagonalFlagGibbs

/-! # Exact sufficiency for diagonal Petz flags -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder CStarAlgebra MatrixOrder
open D5.S3.Quantum.Recovery.BKMFlagRefinement (joint partialTracePetz)
open D5.S3.Quantum.Recovery.LocalCompression.PetzDiagonalFlagGibbs
open private sqrt_diagonal from D5.S3.Quantum.Recovery.LocalCompression.PetzDiagonalFlagGibbs

namespace D5.S3.Quantum.Recovery.LocalCompression.PetzDiagonalFlagSufficiency

variable {n ι κ : Type*} [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A common conditional decoder intertwines the weighted actual Petz blocks.
Summing the intertwining identity gives forward merging and reverse decoding
of the full recovered matrices for arbitrary retained input. -/
theorem partialTracePetz_diagonal_stochastic_sufficiency
    (s : ι → n → ℝ) (W : ι → κ → ℝ) (r : κ → ι → ℝ)
    (hs : ∀ i j, 0 ≤ s i j) (hp : ∀ j, 0 < ∑ i, s i j)
    (hW : ∀ i y, 0 ≤ W i y) (hWsum : ∀ i, ∑ y, W i y = 1)
    (hr : ∀ y i, 0 ≤ r y i) (hrsum : ∀ y, ∑ i, r y i = 1)
    (hdecode : ∀ i y j,
      W i y * effectWeight s i j = r y i * ∑ k, W k y * effectWeight s k j)
    (Q : Matrix n n ℂ) :
    let merged : κ → n → ℝ := fun y j => ∑ i, W i y * s i j
    let old := partialTracePetz (joint (fun i => realDiagonal (s i))) Q
    let new := partialTracePetz (joint (fun y => realDiagonal (merged y))) Q
    let oldBlock := fun i => old.submatrix (fun j => (j, i)) (fun j => (j, i))
    let newBlock := fun y => new.submatrix (fun j => (j, y)) (fun j => (j, y))
    (∀ i y, W i y • oldBlock i = r y i • newBlock y) ∧
      joint (fun y => ∑ i, W i y • oldBlock i) = new ∧
      joint (fun i => ∑ y, r y i • newBlock y) = old := by
  dsimp only
  let merged : κ → n → ℝ := fun y j => ∑ i, W i y * s i j
  change _ ∧
    _ = partialTracePetz (joint (fun y => realDiagonal (merged y))) Q ∧ _
  have hmerged (y : κ) (j : n) : 0 ≤ merged y j :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hW i y) (hs i j))
  have hmarginal (j : n) : ∑ y, merged y j = ∑ i, s i j := by
    simp only [merged]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hWsum, one_mul]
  have hmerged_pos (j : n) : 0 < ∑ y, merged y j := by
    rw [hmarginal]
    exact hp j
  have heffect (y : κ) (j : n) :
      effectWeight merged y j = ∑ i, W i y * effectWeight s i j := by
    simp only [effectWeight, hmarginal, merged, Finset.sum_div, mul_div_assoc]
  let block (a : n → ℝ) := CFC.sqrt (realDiagonal a) * Q * CFC.sqrt (realDiagonal a)
  let oldBlocks := fun i => block (effectWeight s i)
  let newBlocks := fun y => block (effectWeight merged y)
  change (∀ i y, _ • (partialTracePetz (joint (fun i => realDiagonal (s i))) Q).submatrix
      (fun j => (j, i)) (fun j => (j, i)) =
      _ • (partialTracePetz (joint (fun y => realDiagonal (merged y))) Q).submatrix
      (fun j => (j, y)) (fun j => (j, y))) ∧ _ ∧ _
  rw [partialTracePetz_diagonal s hs hp, partialTracePetz_diagonal merged hmerged hmerged_pos]
  have joint_block {α : Type*} [DecidableEq α] (B : α → Matrix n n ℂ) (i : α) :
      (joint B).submatrix (fun j => (j, i)) (fun j => (j, i)) = B i := by
    ext j k
    exact Matrix.blockDiagonal_apply_eq B j k i
  simp only [joint_block]
  change (∀ i y, W i y • oldBlocks i = r y i • newBlocks y) ∧
    joint (fun y => ∑ i, W i y • oldBlocks i) = joint newBlocks ∧
    joint (fun i => ∑ y, r y i • newBlocks y) = joint oldBlocks
  have scale (a : n → ℝ) (ha : ∀ j, 0 ≤ a j) (t : ℝ) (ht : 0 ≤ t) :
      t • block a = block (fun j => t * a j) := by
    dsimp only [block]
    rw [sqrt_diagonal _ ha, sqrt_diagonal _ (fun j => mul_nonneg ht (ha j))]
    ext j k
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Complex.real_smul, Real.sqrt_mul ht, Complex.ofReal_mul]
    have ht' : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht]
    calc
      _ = ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) *
          ((Real.sqrt (a j) : ℂ) * Q j k * (Real.sqrt (a k) : ℂ)) := by rw [ht']
      _ = _ := by ring
  have hblock (i : ι) (y : κ) : W i y • oldBlocks i = r y i • newBlocks y := by
    dsimp only [oldBlocks, newBlocks]
    rw [scale _ (fun j => div_nonneg (hs i j) (hp j).le) _ (hW i y),
      scale _ (fun j => div_nonneg (hmerged y j) (hmerged_pos j).le) _ (hr y i)]
    congr 1
    funext j
    rw [heffect]
    exact hdecode i y j
  refine ⟨hblock, congrArg joint (funext fun y => ?_), congrArg joint (funext fun i => ?_)⟩
  · simp only [hblock, ← Finset.sum_smul, hrsum, one_smul]
  · simp only [← hblock, ← Finset.sum_smul, hWsum, one_smul]

end D5.S3.Quantum.Recovery.LocalCompression.PetzDiagonalFlagSufficiency

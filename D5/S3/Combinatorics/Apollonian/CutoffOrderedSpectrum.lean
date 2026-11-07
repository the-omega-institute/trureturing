/- GID: D5/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apollonian/CutoffOrderedSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Spectrum]
   utility: none
   digest: Ordered second spectrum of the actual unequal old-to-late dilation. -/

import D5.S3.Combinatorics.Apollonian.InnerFaceStages
import D5.S3.SpectralTopology.RectangularDilation

/-! The cutoff blocks retain the actual finite graph's unequal vertex types. -/
noncomputable section
namespace D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum
open InnerFaceStages Matrix

/-- The actual old-to-late symmetric block matrix, with both diagonal blocks zero. -/
def cutoffDilation (k t : ℕ) :
    Matrix (Vertex k ⊕ LateVertex k t) (Vertex k ⊕ LateVertex k t) ℝ :=
  fromBlocks 0 (cutoffBlock k t) (cutoffBlock k t).transpose 0

private theorem cutoff_hermitian (k t : ℕ) : (cutoffDilation k t).IsHermitian := by
  simpa only [cutoffDilation, conjTranspose_eq_transpose_of_trivial] using
    (isHermitian_zero.fromBlocks (B := cutoffBlock k t) rfl isHermitian_zero)

/-- The second decreasing real eigenvalue, with algebraic multiplicity. -/
def cutoffSecond (k t : ℕ) : ℝ :=
  (cutoff_hermitian k t).eigenvalues₀ ⟨1, by
    simp only [Fintype.card_sum]
    have h := card_vertex_ge_four k
    omega⟩

/-- The actual rectangular graph block has the positive second Gram-to-dilation identity. -/
theorem cutoff_second_eq_sqrt_gram (k t : ℕ)
    (hp : 0 < (isHermitian_mul_conjTranspose_self (cutoffBlock k t)).eigenvalues₀
      (secondIndex k)) :
    cutoffSecond k t = Real.sqrt
      ((isHermitian_mul_conjTranspose_self (cutoffBlock k t)).eigenvalues₀ (secondIndex k)) := by
  exact SpectralTopology.RectangularDilation.unequal_real_dilation_second (cutoffBlock k t)
    (by have h := card_vertex_ge_four k; omega) (cutoff_hermitian k t) hp

end D5.S3.Combinatorics.Apollonian.CutoffOrderedSpectrum

/- GID: D5/S3/QuantumChannels/BoundarySaturation
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/BoundarySaturation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For the 2×2 complete-positivity matrix [[1,z],[conj z,p]] of a coherence/population decay pair, positive semidefiniteness forces the coherence RLD boundary ratio |z|² ≤ p, with equality exactly when the matrix is singular (the channel sits at the CP boundary). -/

import Mathlib

namespace D5.S3.QuantumChannels.BoundarySaturation

open Matrix Complex
open scoped ComplexOrder

/-- The 2×2 complete-positivity matrix of a coherence/population decay pair `(z, p)`:
`[[1, z], [conj z, p]]`. Its positive-semidefiniteness is the CP constraint. -/
noncomputable def cpMatrix (z : ℂ) (p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, z; (starRingEnd ℂ) z, (p : ℂ)]

/-- The determinant of the CP matrix is `p − |z|²` (real). -/
theorem cpMatrix_det (z : ℂ) (p : ℝ) :
    (cpMatrix z p).det = ((p - Complex.normSq z : ℝ) : ℂ) := by
  rw [cpMatrix, Matrix.det_fin_two_of]
  rw [Complex.mul_conj]
  push_cast
  ring

/-- Boundary saturation criterion (定理 4.5): if the CP matrix is positive semidefinite,
the coherence RLD boundary ratio satisfies `|z|² ≤ p`. -/
theorem cp_boundary_ratio_le_one (z : ℂ) (p : ℝ) (h : (cpMatrix z p).PosSemidef) :
    Complex.normSq z ≤ p := by
  have hdet := h.det_nonneg
  rw [cpMatrix_det] at hdet
  have hr : (0 : ℝ) ≤ p - Complex.normSq z := by
    rwa [Complex.zero_le_real] at hdet
  linarith

/-- Equality holds exactly at the CP boundary, where the CP matrix is singular
(its determinant vanishes). -/
theorem cp_boundary_eq_iff_det_zero (z : ℂ) (p : ℝ) :
    Complex.normSq z = p ↔ (cpMatrix z p).det = 0 := by
  rw [cpMatrix_det]
  rw [Complex.ofReal_eq_zero]
  constructor
  · intro h; rw [h]; ring
  · intro h; linarith [h]

end D5.S3.QuantumChannels.BoundarySaturation

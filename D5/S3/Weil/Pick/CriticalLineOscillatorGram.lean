/- GID: D5/S3/Weil/Pick/CriticalLineOscillatorGram
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/CriticalLineOscillatorGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Critical-line oscillator resolvents generate a rank-two positive Pick matrix. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/- Library-search audit trail (2026-08-30):
   * Exact repository searches for `CriticalLineOscillator`, `PickMatrix`, and
     the displayed two-resolvent Gram factorization found no existing D5 owner.
   * The nearby frozen Weil modules describe the critical line, scattering,
     Cayley-Laguerre moments, and curvature defects, but do not construct this
     finite Pick matrix.
   * Pinned Mathlib supplies `Matrix.posSemidef_conjTranspose_mul_self` and
     `Fin.sum_univ_two`; the theorem below instantiates them with the two
     reflected critical-line resolvent coordinates. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace D5.S3.Weil.Pick.CriticalLineOscillatorGram

/-- The two rows are the resolvent coordinates of the reflected pole pair
`+i * ordinate` and `-i * ordinate`, sampled at the supplied complex nodes. -/
def criticalLineOscillatorFeatureMatrix {ι : Type*} [Fintype ι]
    (ordinate : ℝ) (nodes : ι → ℂ) : Matrix (Fin 2) ι ℂ :=
  fun row j =>
    ![
      (nodes j - Complex.I * (ordinate : ℂ))⁻¹,
      (nodes j + Complex.I * (ordinate : ℂ))⁻¹
    ] row

/-- The finite kernel matrix obtained by summing the two reflected resolvent
rank-one kernels. -/
def criticalLineOscillatorPickMatrix {ι : Type*} [Fintype ι]
    (ordinate : ℝ) (nodes : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j =>
    star ((nodes i - Complex.I * (ordinate : ℂ))⁻¹) *
        (nodes j - Complex.I * (ordinate : ℂ))⁻¹ +
      star ((nodes i + Complex.I * (ordinate : ℂ))⁻¹) *
        (nodes j + Complex.I * (ordinate : ℂ))⁻¹

/-- Every finite sampling of one reflected critical-line oscillator is exactly
the Gram matrix of its two resolvent coordinates and is therefore positive
semidefinite. -/
theorem critical_line_oscillator_pick_gram
    {ι : Type*} [Fintype ι] (ordinate : ℝ) (nodes : ι → ℂ) :
    criticalLineOscillatorPickMatrix ordinate nodes =
        (criticalLineOscillatorFeatureMatrix ordinate nodes)ᴴ *
          criticalLineOscillatorFeatureMatrix ordinate nodes ∧
      (criticalLineOscillatorPickMatrix ordinate nodes).PosSemidef := by
  have hFactor :
      criticalLineOscillatorPickMatrix ordinate nodes =
        (criticalLineOscillatorFeatureMatrix ordinate nodes)ᴴ *
          criticalLineOscillatorFeatureMatrix ordinate nodes := by
    ext i j
    simp [criticalLineOscillatorPickMatrix,
      criticalLineOscillatorFeatureMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]
  refine ⟨hFactor, ?_⟩
  rw [hFactor]
  exact Matrix.posSemidef_conjTranspose_mul_self _

#print axioms critical_line_oscillator_pick_gram

end D5.S3.Weil.Pick.CriticalLineOscillatorGram

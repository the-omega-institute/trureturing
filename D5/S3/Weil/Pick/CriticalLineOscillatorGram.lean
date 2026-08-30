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
   * Pinned Mathlib supplies `Matrix.posSemidef_conjTranspose_mul_self`; the
     theorem below instantiates it with the two reflected critical-line
     resolvent coordinates. -/

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

/-- The finite Pick atom is the Gram matrix of the two reflected resolvent
coordinates. Entrywise expansion gives the sum of the two associated rank-one
kernels. -/
def criticalLineOscillatorPickMatrix {ι : Type*} [Fintype ι]
    (ordinate : ℝ) (nodes : ι → ℂ) : Matrix ι ι ℂ :=
  (criticalLineOscillatorFeatureMatrix ordinate nodes)ᴴ *
    criticalLineOscillatorFeatureMatrix ordinate nodes

/-- Every finite sampling of one reflected critical-line oscillator has the
stated two-row Gram factorization and is positive semidefinite. -/
theorem critical_line_oscillator_pick_gram
    {ι : Type*} [Fintype ι] (ordinate : ℝ) (nodes : ι → ℂ) :
    criticalLineOscillatorPickMatrix ordinate nodes =
        (criticalLineOscillatorFeatureMatrix ordinate nodes)ᴴ *
          criticalLineOscillatorFeatureMatrix ordinate nodes ∧
      (criticalLineOscillatorPickMatrix ordinate nodes).PosSemidef := by
  refine ⟨rfl, ?_⟩
  simpa only [criticalLineOscillatorPickMatrix] using
    (Matrix.posSemidef_conjTranspose_mul_self
      (criticalLineOscillatorFeatureMatrix ordinate nodes))

#print axioms critical_line_oscillator_pick_gram

end D5.S3.Weil.Pick.CriticalLineOscillatorGram

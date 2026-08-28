/- GID: D5/S3/Weil/ZetaLinear/CriticalDampingGenerator
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaLinear/CriticalDampingGenerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize skew-adjoint normalized diagonal zero generators. -/

import D5.S3.Weil.ZeroSum

namespace D5.S3.Weil.ZetaLinear.CriticalDampingGenerator

open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open scoped ComplexConjugate

/-- The direct-sum fiber over each enumerated zero carries the scalar mode
whose real part is the negative displacement from the critical abscissa and
whose imaginary part is the zero ordinate.  After adding the uniform shift,
this diagonal generator is skew-adjoint exactly on the critical line. -/
theorem normalized_generator_skew_iff_critical_line (Z : ZeroData)
    (omega : {ω : ℝ // (1 / 2 : ℝ) ≤ ω}) :
    (∀ n, (Z.zero n).re = criticalAbscissa) ↔
      ∀ v : Σ n, Fin (Z.multiplicity n),
        starRingEnd ℂ (-((omega + (Z.zero v.1).re - criticalAbscissa : ℝ) : ℂ) +
          Complex.I * ((Z.zero v.1).im : ℂ) + (omega : ℂ)) =
          -(-((omega + (Z.zero v.1).re - criticalAbscissa : ℝ) : ℂ) +
            Complex.I * ((Z.zero v.1).im : ℂ) + (omega : ℂ)) := by
  constructor
  · intro h v
    rw [h v.1]
    rw [criticalAbscissa]
    apply Complex.ext <;> simp
  · intro h n
    have hk : Fin (Z.multiplicity n) := ⟨0, by
      exact Z.multiplicity_pos n⟩
    have hs := h ⟨n, hk⟩
    have hre := congrArg Complex.re hs
    have hstar_re :
        (starRingEnd ℂ (-((omega + (Z.zero n).re - criticalAbscissa : ℝ) : ℂ) +
          Complex.I * ((Z.zero n).im : ℂ) + (omega : ℂ))).re =
          (-((omega + (Z.zero n).re - criticalAbscissa : ℝ) : ℂ) +
            Complex.I * ((Z.zero n).im : ℂ) + (omega : ℂ)).re := by
      rfl
    rw [hstar_re] at hre
    simp only [Complex.add_re, Complex.neg_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im] at hre
    rw [criticalAbscissa] at hre ⊢
    linarith

end D5.S3.Weil.ZetaLinear.CriticalDampingGenerator

/- GID: D5/S3/Zeros/Symmetry/BarycenterDefectDecomposition
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/BarycenterDefectDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Completion coordinates characterize critical zeros and split mirror pairs. -/

import D5.S3.Zeros.Symmetry.ZeroSymmetryAction

namespace D5.S3.Zeros.Symmetry.BarycenterDefectDecomposition

open D5.S3.Weil.Convention
open D5.S3.Weil.ReflectionLedger
open D5.S3.Weil.ZeroSum

/-- The midpoint of a complex coordinate and its conjugate reflection. -/
noncomputable def completionBarycenter (rho : ℂ) : ℂ :=
  (rho + mirror rho) / 2

/-- The signed displacement from the conjugate-reflection midpoint. -/
noncomputable def antiCoordinate (rho : ℂ) : ℂ :=
  (rho - mirror rho) / 2

/-- Vanishing anti-coordinate is equivalent to the critical-line condition.
A nonzero symmetric displacement produces a two-point mirror orbit whose
barycenter is fixed and whose two points have the stated radius. -/
theorem barycenter_defect_decomposition :
    ((∀ {rho : ℂ}, IsNontrivialZero rho → rho.re = criticalAbscissa) ↔
      ∀ {rho : ℂ}, IsNontrivialZero rho → antiCoordinate rho = 0) ∧
    ∀ delta gamma : ℝ, delta ≠ 0 →
      let right : ℂ :=
        ((criticalAbscissa + delta : ℝ) : ℂ) + Complex.I * (gamma : ℂ)
      let left : ℂ :=
        ((criticalAbscissa - delta : ℝ) : ℂ) + Complex.I * (gamma : ℂ)
      let center : ℂ :=
        (criticalAbscissa : ℂ) + Complex.I * (gamma : ℂ)
      completionBarycenter right = center ∧
        completionBarycenter left = center ∧
        antiCoordinate right = (delta : ℂ) ∧
        antiCoordinate left = -(delta : ℂ) ∧
        mirror right = left ∧
        mirror left = right ∧
        ({right, mirror right} : Finset ℂ).card = 2 ∧
        ‖right - center‖ = |delta| ∧
        ‖left - center‖ = |delta| := by
  constructor
  · constructor
    · intro hcritical rho hrho
      have hline := hcritical hrho
      have hfixed : rho = mirror rho := by
        apply Complex.ext
        · simp [mirror, reflection, hline, criticalAbscissa]
          norm_num
        · simp [mirror, reflection]
      rw [antiCoordinate, ← hfixed]
      ring
    · intro hanti rho hrho
      have hzero := hanti hrho
      have hsub : rho - mirror rho = 0 := by
        simpa [antiCoordinate] using hzero
      exact mirror_fixed_re_eq rho (sub_eq_zero.mp hsub).symm
  · intro delta gamma hdelta
    dsimp
    have hmirrorRight :
        mirror
            (((criticalAbscissa + delta : ℝ) : ℂ) +
              Complex.I * (gamma : ℂ)) =
          ((criticalAbscissa - delta : ℝ) : ℂ) +
            Complex.I * (gamma : ℂ) := by
      apply Complex.ext
      · simp [mirror, reflection, criticalAbscissa]
        ring
      · simp [mirror, reflection]
    have hmirrorLeft :
        mirror
            (((criticalAbscissa - delta : ℝ) : ℂ) +
              Complex.I * (gamma : ℂ)) =
          ((criticalAbscissa + delta : ℝ) : ℂ) +
            Complex.I * (gamma : ℂ) := by
      apply Complex.ext
      · simp [mirror, reflection, criticalAbscissa]
        ring
      · simp [mirror, reflection]
    have hne :
        (((criticalAbscissa + delta : ℝ) : ℂ) +
            Complex.I * (gamma : ℂ)) ≠
          ((criticalAbscissa - delta : ℝ) : ℂ) +
            Complex.I * (gamma : ℂ) := by
      intro h
      have hre := congrArg Complex.re h
      simp [criticalAbscissa] at hre
      exact hdelta (by linarith)
    refine ⟨?_, ?_, ?_, ?_, hmirrorRight, hmirrorLeft, ?_, ?_, ?_⟩
    · rw [completionBarycenter, hmirrorRight]
      apply Complex.ext
      · simp [criticalAbscissa]
      · simp [criticalAbscissa]
    · rw [completionBarycenter, hmirrorLeft]
      apply Complex.ext
      · simp [criticalAbscissa]
      · simp [criticalAbscissa]
    · rw [antiCoordinate, hmirrorRight]
      apply Complex.ext
      · simp [criticalAbscissa]
      · simp [criticalAbscissa]
    · rw [antiCoordinate, hmirrorLeft]
      apply Complex.ext
      · simp [criticalAbscissa]
        ring
      · simp [criticalAbscissa]
    · rw [hmirrorRight]
      exact Finset.card_pair hne
    · rw [show
          (((criticalAbscissa + delta : ℝ) : ℂ) +
              Complex.I * (gamma : ℂ)) -
              ((criticalAbscissa : ℂ) + Complex.I * (gamma : ℂ)) =
            (delta : ℂ) by
          apply Complex.ext
          · simp
          · simp]
      simp
    · rw [show
          (((criticalAbscissa - delta : ℝ) : ℂ) +
              Complex.I * (gamma : ℂ)) -
              ((criticalAbscissa : ℂ) + Complex.I * (gamma : ℂ)) =
            -(delta : ℂ) by
          apply Complex.ext
          · simp
          · simp]
      simp

end D5.S3.Zeros.Symmetry.BarycenterDefectDecomposition

/- GID: D5/S3/Midline/OffLineCoefficientScaling
   generality: I
   mirror-B: D5/B/S3/Midline/OffLineCoefficientScaling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Off-line coefficients split into density, phase, and scaling factors. -/

import D5.S3.Midline.OffLineScaling

namespace D5.S3.Midline.OffLineCoefficientScaling

open D5.S3.Weil.Convention D5.S3.Weil.LabeledZeta
open D5.S3.Weil.ReflectionLedger D5.S3.Zeros.ZeroGeometry
open D5.S3.Midline.OffLineScaling

/-- The coordinatewise coefficient at `s = 1/2 + delta + i t` splits into
half-density, phase, and off-line scaling factors. Its scaling ledger is
`delta * length`, positive-length entries have one sign and unbounded natural
multiples when `delta` is nonzero, and unit rotations preserve every modulus.
No assertion about a sum after analytic continuation is made here. -/
theorem off_line_coefficient_scaling_spec {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (delta t : ℝ) (hDelta : delta ≠ 0) :
    let s : ℂ := ((criticalAbscissa + delta : ℝ) : ℂ) + (t : ℂ) * Complex.I
    (∀ a,
        labeledZeta length s a =
          Complex.exp (-(criticalAbscissa : ℂ) * (length a : ℂ)) *
            Complex.exp (-((t : ℂ) * Complex.I) * (length a : ℂ)) *
              Complex.exp (-(delta : ℂ) * (length a : ℂ))) ∧
      (∀ a, scalingLedger length s a = delta * length a) ∧
      (s.re ≠ criticalAbscissa ∧
        (∀ a, 0 < length a → scalingLedger length s a ≠ 0) ∧
        (∀ a b, 0 < length a → 0 < length b →
          (0 < scalingLedger length s a ↔ 0 < scalingLedger length s b)) ∧
        (∀ (a : A) (m : ℕ),
          scalingLedger length s (m • a) = m * scalingLedger length s a) ∧
        ∀ a, 0 < length a → ∀ C : ℝ, ∃ m : ℕ,
          C < |scalingLedger length s (m • a)|) ∧
      ∀ (u : ℂ), ‖u‖ = 1 → ∀ a,
        ‖u * labeledZeta length s a‖ = ‖labeledZeta length s a‖ := by
  dsimp
  have hOff :
      ((((criticalAbscissa + delta : ℝ) : ℂ) + (t : ℂ) * Complex.I).re) ≠
        criticalAbscissa := by
    simp [hDelta]
  refine ⟨?_, ?_, ⟨hOff, off_line_scaling_ledger_growth length _ hOff⟩, ?_⟩
  · intro a
    simp only [labeledZeta]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp [criticalAbscissa]
    ring
  · intro a
    simp [scalingLedger]
  · intro u hu a
    rw [norm_mul, hu, one_mul]

end D5.S3.Midline.OffLineCoefficientScaling

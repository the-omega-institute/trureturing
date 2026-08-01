/- GID: D5/S3/Midline/DualCharacterization
   generality: I
   mirror-B: D5/B/S3/Midline/DualCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equate mirror fixed points, unitary parameters, and the critical line. -/

import D5.S3.Weil.SpectralDynamics

namespace D5.S3.Midline.DualCharacterization

open D5.S3.Weil.Convention D5.S3.Weil.LabeledZeta
open D5.S3.Weil.ReflectionLedger D5.S3.Weil.CriticalLine
open D5.S3.Weil.SpectralDynamics

/-- Conjugate-reflection fixed points and unitary half-density parameters are the same
critical line. -/
theorem midline_dual_characterization {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (hNontrivial : ∃ a, length a ≠ 0) :
    {s : ℂ | mirror s = s} =
        {s : ℂ | ∀ a, ‖halfDensityReading length s a‖ = 1} ∧
      {s : ℂ | mirror s = s} =
        {s : ℂ | s.re = criticalAbscissa} := by
  constructor
  · ext s
    have h := critical_line_characterizations length hNontrivial s
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, eq_comm, h.1, h.2.1]
  · ext s
    have h := critical_line_characterizations length hNontrivial s
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, eq_comm, h.1]

end D5.S3.Midline.DualCharacterization

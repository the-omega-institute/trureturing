/- GID: D5/S3/Weil/ReflectionLedger
   generality: I
   mirror-B: D5/B/S3/Weil/ReflectionLedger
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conjugate reflection reverses scaling ledgers and fixes the critical line. -/

import D5.S3.Weil.LabeledZeta

namespace D5.S3.Weil.ReflectionLedger

open D5.S3.Weil.Convention D5.S3.Weil.LabeledZeta
open scoped ComplexConjugate

/-- Reflection across one in the spectral parameter. -/
def reflection (s : ℂ) : ℂ := 1 - s

/-- Reflection composed with complex conjugation. -/
def mirror (s : ℂ) : ℂ := reflection (conj s)

/-- The displacement from the critical line, weighted by ledger length. -/
noncomputable def scalingLedger {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (s : ℂ) (a : A) : ℝ :=
  (s.re - criticalAbscissa) * length a

/-- Every fixed point of conjugate reflection lies on the critical line. -/
theorem mirror_fixed_re_eq (s : ℂ) (hfixed : mirror s = s) :
    s.re = criticalAbscissa := by
  have hre := congrArg Complex.re hfixed
  simp [mirror, reflection] at hre
  rw [criticalAbscissa]
  linarith

/-- Mirroring negates every scaling entry, and its fixed locus is the critical line. -/
theorem mirror_reversal_spec {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (s : ℂ) :
    (∀ a, scalingLedger length (mirror s) a = -scalingLedger length s a) ∧
      (s = mirror s ↔ s.re = criticalAbscissa) := by
  constructor
  · intro a
    simp [scalingLedger, mirror, reflection, criticalAbscissa]
    ring
  · constructor
    · intro hfixed
      exact mirror_fixed_re_eq s hfixed.symm
    · intro hre
      apply Complex.ext
      · simp [mirror, reflection, hre, criticalAbscissa]
        norm_num
      · simp [mirror, reflection]

end D5.S3.Weil.ReflectionLedger

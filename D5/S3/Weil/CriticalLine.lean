/- GID: D5/S3/Weil/CriticalLine
   generality: I
   mirror-B: D5/B/S3/Weil/CriticalLine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize the critical line by half-density unitarity and a zero scaling ledger. -/

import D5.S3.Weil.ReflectionLedger

namespace D5.S3.Weil.CriticalLine

open D5.S3.Weil.Convention D5.S3.Weil.LabeledZeta
open D5.S3.Weil.ReflectionLedger

/-- The labeled heat trace after normalization by the critical half-density. -/
noncomputable def halfDensityReading {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (s : ℂ) (a : A) : ℂ :=
  Complex.exp ((criticalAbscissa : ℂ) * (length a : ℂ)) * labeledZeta length s a

/-- The normalized modulus is the exponential of the negated scaling entry. -/
theorem half_density_reading_norm {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (s : ℂ) (a : A) :
    ‖halfDensityReading length s a‖ = Real.exp (-scalingLedger length s a) := by
  rw [halfDensityReading, norm_mul, Complex.norm_exp, labeledZeta]
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp [scalingLedger]
  ring

/-- A nontrivial ledger is unitary after half-density normalization exactly on the critical line. -/
theorem unitarity_line_iff {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (hNontrivial : ∃ a, length a ≠ 0) (s : ℂ) :
    ((∀ a, scalingLedger length s a = 0) ↔
      ∀ a, ‖halfDensityReading length s a‖ = 1) ∧
    ((∀ a, ‖halfDensityReading length s a‖ = 1) ↔
      s.re = criticalAbscissa) := by
  obtain ⟨a₀, ha₀⟩ := hNontrivial
  have hScaling : (∀ a, scalingLedger length s a = 0) ↔
      s.re = criticalAbscissa := by
    constructor
    · intro h
      have h₀ := h a₀
      rcases mul_eq_zero.mp h₀ with hs | ha
      · exact sub_eq_zero.mp hs
      · exact (ha₀ ha).elim
    · intro hs a
      simp [scalingLedger, hs]
  have hUnitary : (∀ a, ‖halfDensityReading length s a‖ = 1) ↔
      s.re = criticalAbscissa := by
    constructor
    · intro h
      have h₀ := h a₀
      rw [half_density_reading_norm] at h₀
      have hzero : -scalingLedger length s a₀ = 0 := by
        apply Real.exp_injective
        simpa using h₀
      have hscale : scalingLedger length s a₀ = 0 := neg_eq_zero.mp hzero
      rcases mul_eq_zero.mp hscale with hs | ha
      · exact sub_eq_zero.mp hs
      · exact (ha₀ ha).elim
    · intro hs a
      rw [half_density_reading_norm]
      simp [scalingLedger, hs]
  exact ⟨hScaling.trans hUnitary.symm, hUnitary⟩

end D5.S3.Weil.CriticalLine

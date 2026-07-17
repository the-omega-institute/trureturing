/- GID: D5/S3/Weil/ZeroGeometry
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separate projected zeta cancellation from local and mirror-paired scaling balance. -/

import D5.S3.Weil.CriticalLine
import D5.S3.Weil.ZeroSum

namespace D5.S3.Weil.ZeroGeometry

open D5.S3.Weil.Convention
open D5.S3.Weil.CriticalLine
open D5.S3.Weil.LabeledZeta
open D5.S3.Weil.ReflectionLedger
open D5.S3.Weil.ZeroSum
open scoped ComplexConjugate

/-- A projected zeta zero does not erase its coordinatewise labeled vector. -/
theorem projection_zero_labeled_vector_spec {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (rho : ℂ) (hZero : classicalZeta rho = 0) :
    classicalZeta rho = 0 ∧ labeledZeta length rho ≠ 0 := by
  exact ⟨hZero, labeled_zeta_vector_ne_zero length rho⟩

/-- Positive-length entries detect both sides of the critical-line displacement. -/
theorem off_line_scaling_entry_spec {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (s : ℂ) (a : A) (ha : 0 < length a) :
    scalingLedger length s a = (s.re - criticalAbscissa) * length a ∧
      (scalingLedger length s a ≠ 0 ↔ s.re ≠ criticalAbscissa) ∧
      (0 < scalingLedger length s a ↔ criticalAbscissa < s.re) ∧
      (scalingLedger length s a < 0 ↔ s.re < criticalAbscissa) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · constructor
    · intro hScaling hLine
      apply hScaling
      simp [scalingLedger, hLine]
    · intro hLine
      exact mul_ne_zero (sub_ne_zero.mpr hLine) (ne_of_gt ha)
  · constructor
    · intro hScaling
      rw [scalingLedger] at hScaling
      nlinarith
    · intro hLine
      exact mul_pos (sub_pos.mpr hLine) ha
  · constructor
    · intro hScaling
      rw [scalingLedger] at hScaling
      nlinarith
    · intro hLine
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hLine) ha

/-- An address-independent factor can clear every normalized entry only on the line. -/
theorem global_factor_clearing_forces_critical_line {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (hNontrivial : ∃ a, length a ≠ 0)
    (s : ℂ) (c : ℂ)
    (hClear : ∀ a, ‖c * halfDensityReading length s a‖ = 1) :
    s.re = criticalAbscissa := by
  have hc : ‖c‖ = 1 := by
    simpa [halfDensityReading, labeledZeta] using hClear (0 : A)
  apply ((unitarity_line_iff length hNontrivial s).2).mp
  intro a
  have h := hClear a
  rw [norm_mul, hc, one_mul] at h
  exact h

/-- The stored zeta symmetries form the mirror quartet and cancel scaling crosswise. -/
theorem zero_quartet_scaling_spec (Z : ZeroData) (n : ℕ)
    {A : Type*} [AddMonoid A] (length : LedgerLength A) :
    let rho := Z.zero n
    Z.zero (Z.conjugation n) = conj rho ∧
      Z.zero (Z.reflection n) = 1 - rho ∧
      Z.zero (Z.conjugation (Z.reflection n)) = mirror rho ∧
      ∀ a, scalingLedger length
          (Z.zero (Z.conjugation (Z.reflection n))) a =
        -scalingLedger length rho a := by
  dsimp
  have hMirror :
      Z.zero (Z.conjugation (Z.reflection n)) = mirror (Z.zero n) := by
    rw [Z.zero_conjugation, Z.zero_reflection]
    simp [mirror, reflection]
  refine ⟨Z.zero_conjugation n, Z.zero_reflection n, hMirror, ?_⟩
  intro a
  rw [hMirror]
  exact (mirror_reversal_spec length (Z.zero n)).1 a

/-- Off-line mirror partners are distinct but their scaling entries cancel crosswise. -/
theorem mirror_pair_distinct_iff_off_line_and_cancels {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (s : ℂ) :
    (s ≠ mirror s ↔ s.re ≠ criticalAbscissa) ∧
      ∀ a, scalingLedger length s a + scalingLedger length (mirror s) a = 0 := by
  refine ⟨?_, ?_⟩
  · exact not_congr (mirror_reversal_spec length s).2
  · intro a
    rw [(mirror_reversal_spec length s).1 a]
    ring

/-- A projected zero is ontological only when every local scaling entry is balanced. -/
def IsOntologicalZero {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (closedAt : ℂ → Prop) (rho : ℂ) : Prop :=
  classicalZeta rho = 0 ∧
    (∀ a, scalingLedger length rho a = 0) ∧
    closedAt rho

/-- Local balance on a nontrivial ledger places an ontological zero on the line. -/
theorem ontological_zero_re_eq_critical {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (hNontrivial : ∃ a, length a ≠ 0)
    (closedAt : ℂ → Prop) (rho : ℂ)
    (hZero : IsOntologicalZero length closedAt rho) :
    rho.re = criticalAbscissa := by
  obtain ⟨a, ha⟩ := hNontrivial
  have hScaling := hZero.2.1 a
  rw [scalingLedger] at hScaling
  rcases mul_eq_zero.mp hScaling with hLine | hLength
  · exact sub_eq_zero.mp hLine
  · exact (ha hLength).elim

end D5.S3.Weil.ZeroGeometry

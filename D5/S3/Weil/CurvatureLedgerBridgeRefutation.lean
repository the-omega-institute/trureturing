/- GID: D5/S3/Weil/CurvatureLedgerBridgeRefutation
   generality: I
   mirror-B: D5/B/S3/Weil/CurvatureLedgerBridgeRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refute a global curvature-ledger bridge by two frozen-definition
     toy readouts with incompatible support and mass. -/

import D5.S3.Analytic.Boundary.InteriorCurvatureCriterion
import D5.S3.Weil.LedgerDeficitSecondVariation

/- Library-search audit trail (2026-09-01):
   * Repository and pinned-Mathlib searches found no existing theorem comparing
     the frozen curvature and zero-deficit atomic measures.
   * The curvature specialization below copies the source location
     `-im(rho) + I * (re(rho) - 1/2)` and the unit-multiplicity source weight
     `ENNReal.ofReal (2*pi)` literally from `interior_curvature_criterion`.
   * The deficit specialization only pairs the already frozen
     `zeroDeficitMeasure` at a zero and its mirror.
   * Pinned Mathlib supplies `Measure.smul_apply`, `Measure.dirac_apply`, and
     `ENNReal.ofReal_eq_ofReal_iff`; singleton and universal-set evaluations
     below use those standard measure identities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.CurvatureLedgerBridgeRefutation

open Complex MeasureTheory Set
open scoped ENNReal

open D5.S3.Weil.Convention
open D5.S3.Weil.LedgerDeficitSecondVariation
open D5.S3.Weil.ReflectionLedger

/-- The unit-multiplicity curvature atom, specialized literally from the
frozen curvature criterion. -/
def unitCurvatureAtom (rho : ℂ) : Measure ℂ :=
  ENNReal.ofReal (2 * Real.pi) • Measure.dirac
    ((-rho.im : ℂ) + Complex.I * ((rho.re - (1 : ℝ) / 2 : ℝ) : ℂ))

/-- The frozen zero-deficit readout for a mirror pair. -/
def zeroDeficitPair (rho : ℂ) : Measure ℂ :=
  zeroDeficitMeasure rho + zeroDeficitMeasure (mirror rho)

/-- On the W-B1 pair `{3/4, 1/4}`, the right zero produces the curvature
atom of mass `2*pi` at `I/4`. -/
theorem first_curvature_readout :
    unitCurvatureAtom (((3 : ℝ) / 4 : ℝ) : ℂ) =
      ENNReal.ofReal (2 * Real.pi) • Measure.dirac (Complex.I / 4) := by
  simp [unitCurvatureAtom]
  ring

/-- On the W-B1 pair `{3/4, 1/4}`, the frozen ledger construction produces
mass `1/32` at each original spectral address. -/
theorem first_deficit_readout :
    zeroDeficitPair (((3 : ℝ) / 4 : ℝ) : ℂ) =
      ENNReal.ofReal ((1 : ℝ) / 32) •
          Measure.dirac (((3 : ℝ) / 4 : ℝ) : ℂ) +
      ENNReal.ofReal ((1 : ℝ) / 32) •
          Measure.dirac (((1 : ℝ) / 4 : ℝ) : ℂ) := by
  have hmirror :
      mirror (((3 : ℝ) / 4 : ℝ) : ℂ) = (((1 : ℝ) / 4 : ℝ) : ℂ) := by
    rw [mirror, Complex.conj_ofReal]
    apply Complex.ext <;> norm_num [reflection]
  have hweight (rho : ℂ) :
      zeroDeficitMeasure rho =
        ENNReal.ofReal
          (2 * (2 * (rho.re - criticalAbscissa) ^ 2) ^ 2) •
            Measure.dirac rho := by
    simp [zeroDeficitMeasure, scalarToDeficitMeasure,
      ledger_deficit_second_variation_eq, zero_addressed_scaling_eq]
  rw [zeroDeficitPair, hmirror, hweight, hweight]
  norm_num [criticalAbscissa]

/-- On the second pair `{1, 0}`, the right zero produces the curvature atom
of mass `2*pi` at `I/2`. -/
theorem second_curvature_readout :
    unitCurvatureAtom (1 : ℂ) =
      ENNReal.ofReal (2 * Real.pi) • Measure.dirac (Complex.I / 2) := by
  simp [unitCurvatureAtom]
  ring

/-- On the second pair `{1, 0}`, the frozen ledger construction produces
mass `1/2` at each original spectral address. -/
theorem second_deficit_readout :
    zeroDeficitPair (1 : ℂ) =
      ENNReal.ofReal ((1 : ℝ) / 2) • Measure.dirac (1 : ℂ) +
      ENNReal.ofReal ((1 : ℝ) / 2) • Measure.dirac (0 : ℂ) := by
  have hmirror : mirror (1 : ℂ) = (0 : ℂ) := by
    apply Complex.ext <;> norm_num [mirror, reflection]
  have hweight (rho : ℂ) :
      zeroDeficitMeasure rho =
        ENNReal.ofReal
          (2 * (2 * (rho.re - criticalAbscissa) ^ 2) ^ 2) •
            Measure.dirac rho := by
    simp [zeroDeficitMeasure, scalarToDeficitMeasure,
      ledger_deficit_second_variation_eq, zero_addressed_scaling_eq]
  rw [zeroDeficitPair, hmirror, hweight, hweight]
  norm_num [criticalAbscissa]

/-- The two total-mass readouts cannot be reconciled by one global
normalization: the first deficit pair has mass `1/16`, while the second has
mass `1`, and both curvature atoms have mass `2*pi`. -/
theorem no_global_mass_normalization :
    ¬ ∃ c : ℝ≥0∞,
      c * (16 : ℝ≥0∞)⁻¹ = 2 * ENNReal.ofReal Real.pi ∧
      c = 2 * ENNReal.ofReal Real.pi := by
  rintro ⟨c, hfirst, hsecond⟩
  rw [hsecond] at hfirst
  have hreal := congrArg ENNReal.toReal hfirst
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal Real.pi_pos.le] at hreal

/-- Kernelized W-B3 verdict: the two literal frozen-definition readouts admit
no single global scalar that turns both deficit measures into their curvature
measures. -/
theorem curvature_ledger_bridge_refuted :
    ¬ ∃ c : ℝ≥0∞,
      c • zeroDeficitPair (((3 : ℝ) / 4 : ℝ) : ℂ) =
          unitCurvatureAtom (((3 : ℝ) / 4 : ℝ) : ℂ) ∧
      c • zeroDeficitPair (1 : ℂ) = unitCurvatureAtom (1 : ℂ) := by
  rintro ⟨c, hfirst, hsecond⟩
  apply no_global_mass_normalization
  refine ⟨c, ?_, ?_⟩
  · have h := congrArg (fun measure : Measure ℂ => measure Set.univ) hfirst
    rw [first_deficit_readout, first_curvature_readout] at h
    simp [Measure.smul_apply, ← mul_add] at h
    have hsum : (32⁻¹ + 32⁻¹ : ℝ≥0∞) = 16⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
      rw [ENNReal.toReal_add (by norm_num) (by norm_num)]
      simp [ENNReal.toReal_inv]
      norm_num
    rw [hsum] at h
    exact h
  · have h := congrArg (fun measure : Measure ℂ => measure Set.univ) hsecond
    rw [second_deficit_readout, second_curvature_readout] at h
    simp [Measure.smul_apply, ← mul_add] at h
    have hsum : (2⁻¹ + 2⁻¹ : ℝ≥0∞) = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
      rw [ENNReal.toReal_add (by norm_num) (by norm_num)]
      simp [ENNReal.toReal_inv]
      norm_num
    rw [hsum, mul_one] at h
    exact h

#print axioms first_curvature_readout
#print axioms first_deficit_readout
#print axioms second_curvature_readout
#print axioms second_deficit_readout
#print axioms no_global_mass_normalization
#print axioms curvature_ledger_bridge_refuted

end D5.S3.Weil.CurvatureLedgerBridgeRefutation

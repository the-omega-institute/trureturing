/- GID: D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Same-height conjugate reflection preserves positive zero windows. -/

import D5.S3.Weil.ZetaRvm.Halving
import D5.S3.Zeros.CompletedZeta

/- Library-search audit trail (2026-09-01):
   * Repository searches for `Blaschke`, `criticalLineMirror`, `mirror`,
     `reflect_reflect`, `reflect_mem_window`, and abstract conjugation and
     functional-equation hypotheses found exact frozen components but no
     single declaration packaging the source atom's reflection substrate.
   * `Zeta23.reflect_reflect`, `Zeta23.reflect_im`, and `Zeta23.reflect_re`
     supply the involution and coordinate laws. `mirror_reversal_spec`
     supplies the fixed-line equivalence, and `zero_quartet_scaling_spec`
     supplies the abstract zero-stability implication used below.
   * Pinned Mathlib supplies `Complex.conj_re`, `Complex.conj_im`, complex
     extensionality, and ring normalization. Searches for a packaged
     conjugate-reflection fixed-line theorem found no Mathlib hit.
   * The source counts zeros with multiplicity. This module proves only the
     pointwise zero and positive-window stability needed for the algebraic
     reflection layer; no multiplicity-preservation claim is made. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.Symmetry.FiniteShiftedBlaschkeSymmetry

open D5.S3.Weil.Convention
open D5.S3.Weil.LabeledZeta
open D5.S3.Weil.ReflectionLedger
open D5.S3.Zeros.CompletedZeta
open scoped ComplexConjugate

/-- The same-height conjugate reflection is involutive, preserves the
ordinate, reverses signed displacement from the critical line, and fixes
exactly that line. -/
theorem critical_line_mirror_spec (rho : ℂ) :
    Zeta23.reflect (Zeta23.reflect rho) = rho ∧
      (Zeta23.reflect rho).im = rho.im ∧
      (Zeta23.reflect rho).re - (1 : ℝ) / 2 =
        -(rho.re - (1 : ℝ) / 2) ∧
      (Zeta23.reflect rho = rho ↔ rho.re = (1 : ℝ) / 2) := by
  refine ⟨Zeta23.reflect_reflect rho, Zeta23.reflect_im rho, ?_, ?_⟩
  · rw [Zeta23.reflect_re]
    ring
  · simpa [Zeta23.reflect, mirror, reflection, criticalAbscissa,
      Complex.star_def, eq_comm] using
      (mirror_reversal_spec (0 : LedgerLength ℕ) rho).2

/-- Functional equation and conjugation covariance imply that the
same-height mirror of a zero is again a zero. The positive-ordinate window
`0 < Im rho ≤ T` is preserved pointwise. -/
theorem finite_shifted_blaschke_reflection_spec
    (xi : ℂ → ℂ)
    (hfe : ∀ s, xi (1 - s) = xi s)
    (hconj : ∀ s, xi (conj s) = conj (xi s))
    (T : ℝ) (_hT : 0 < T) (rho : ℂ) :
    (Zeta23.reflect (Zeta23.reflect rho) = rho ∧
      (Zeta23.reflect rho).im = rho.im ∧
      (Zeta23.reflect rho).re - (1 : ℝ) / 2 =
        -(rho.re - (1 : ℝ) / 2) ∧
      (Zeta23.reflect rho = rho ↔ rho.re = (1 : ℝ) / 2)) ∧
    (xi rho = 0 → xi (Zeta23.reflect rho) = 0) ∧
    (0 < rho.im ∧ rho.im ≤ T →
      0 < (Zeta23.reflect rho).im ∧ (Zeta23.reflect rho).im ≤ T) := by
  refine ⟨critical_line_mirror_spec rho, ?_, ?_⟩
  · intro hzero
    have hspec :=
      zero_quartet_scaling_spec xi hconj hfe
        (0 : LedgerLength ℕ) rho hzero
    simpa [Zeta23.reflect, Complex.star_def] using hspec.2.2.2.1
  · intro hwindow
    simpa only [Zeta23.reflect_im] using hwindow

/-- The point `1/2 + 3i` lies on the critical line and is fixed by the
same-height mirror, whose ordinate remains three. -/
theorem critical_line_witness :
    let rho : ℂ := (1 / 2 : ℂ) + 3 * Complex.I
    (Zeta23.reflect (Zeta23.reflect rho) = rho ∧
      (Zeta23.reflect rho).im = rho.im ∧
      (Zeta23.reflect rho).re - (1 : ℝ) / 2 =
        -(rho.re - (1 : ℝ) / 2) ∧
      (Zeta23.reflect rho = rho ↔ rho.re = (1 : ℝ) / 2)) ∧
    Zeta23.reflect rho = rho ∧ (Zeta23.reflect rho).im = 3 := by
  dsimp only
  refine ⟨critical_line_mirror_spec _, ?_, ?_⟩
  · apply Complex.ext <;>
      norm_num [Zeta23.reflect, Complex.star_def]
  · norm_num [Zeta23.reflect, Complex.star_def]

/-- The point `3/4 + 3i` is mirrored to `1/4 + 3i`; it is not fixed, while
all four structural mirror laws and ordinate preservation still hold. -/
theorem off_line_witness :
    let rho : ℂ := (3 / 4 : ℂ) + 3 * Complex.I
    let sigmaRho : ℂ := (1 / 4 : ℂ) + 3 * Complex.I
    (Zeta23.reflect (Zeta23.reflect rho) = rho ∧
      (Zeta23.reflect rho).im = rho.im ∧
      (Zeta23.reflect rho).re - (1 : ℝ) / 2 =
        -(rho.re - (1 : ℝ) / 2) ∧
      (Zeta23.reflect rho = rho ↔ rho.re = (1 : ℝ) / 2)) ∧
    Zeta23.reflect rho = sigmaRho ∧ Zeta23.reflect rho ≠ rho ∧
      (Zeta23.reflect rho).im = 3 := by
  dsimp only
  refine ⟨critical_line_mirror_spec _, ?_, ?_, ?_⟩
  · apply Complex.ext
    · rw [Zeta23.reflect_re]
      norm_num
    · rw [Zeta23.reflect_im]
      norm_num
  · intro hfixed
    have hre := congrArg Complex.re hfixed
    rw [Zeta23.reflect_re] at hre
    norm_num at hre
  · rw [Zeta23.reflect_im]
    norm_num

#print axioms critical_line_mirror_spec
#print axioms finite_shifted_blaschke_reflection_spec
#print axioms critical_line_witness
#print axioms off_line_witness

end D5.S3.Zeros.Symmetry.FiniteShiftedBlaschkeSymmetry

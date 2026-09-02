/- GID: D5/S3/Zeros/Symmetry/CriticalLineStabilizerOrbit
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/CriticalLineStabilizerOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Critical localization fixes mirror indices; off-line zeros have four-point orbits. -/

import D5.S3.Analytic.Zeta.RealUnitIntervalZetaNonvanishing
import D5.S3.Zeros.Symmetry.ZeroOrbitCardinality

/-! Library and repository search audit (2026-09-03):
* `ZeroSymmetryAction.mirror_index_fixed_iff_critical` is the exact public
  fixed-point equivalence and `zero_symmetries_commute` is the exact public
  symmetry-preservation result.
* `ZeroOrbitCardinality.zero_orbit_card_four_of_off_line` supplies the exact
  four-point conclusion once conjugation is known to move the index.
* Pinned Mathlib has no open-critical-strip real-axis zeta nonvanishing
  theorem. `RealUnitIntervalZetaNonvanishing` supplies that prerequisite and
  excludes a conjugation-fixed index directly from the `ZeroData` fields.
* The statement uses localization of the supplied exhaustive zero data rather
  than Mathlib's global Riemann-hypothesis proposition. This keeps the two
  alternatives on the same carrier and needs no converse bridge from a global
  negation to an enumerated off-line zero.
-/

namespace D5.S3.Zeros.Symmetry.CriticalLineStabilizerOrbit

open D5.S3.Analytic.Zeta.RealUnitIntervalZetaNonvanishing
open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open D5.S3.Zeros.Symmetry.ZeroOrbitCardinality
open D5.S3.Zeros.Symmetry.ZeroSymmetryAction
open scoped ComplexConjugate

/-- Critical localization is mirror fixedness; outside it, an enumerated zero
has a four-point orbit, while the two zero symmetries continue to commute. -/
theorem critical_line_stabilizer_orbit_dichotomy (Z : ZeroData) :
    ((∀ n, (Z.zero n).re = criticalAbscissa) ↔
      ∀ n, Z.conjugation (Z.reflection n) = n) ∧
    ((¬ ∀ n, (Z.zero n).re = criticalAbscissa) →
      ∃ n, ({n, Z.reflection n, Z.conjugation n,
        Z.conjugation (Z.reflection n)} : Finset ℕ).card = 4) ∧
    Function.Commute Z.reflection Z.conjugation := by
  have hconjugation (n : ℕ) : Z.conjugation n ≠ n := by
    intro hfixed
    have hzero := Z.zero_conjugation n
    rw [hfixed] at hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.conj_im] at him
    have him_zero : (Z.zero n).im = 0 := by linarith
    have hzeta : riemannZeta ((Z.zero n).re : ℂ) = 0 := by
      have hnontrivial := (Z.zero_isNontrivial n).1
      have hreal : Z.zero n = ((Z.zero n).re : ℂ) := by
        apply Complex.ext <;> simp [him_zero]
      rw [hreal] at hnontrivial
      simpa [classicalZeta] using hnontrivial
    exact (riemannZeta_ne_zero_on_real_unit_interval (Z.zero n).re
      (Z.zero_isNontrivial n).2.1 (Z.zero_isNontrivial n).2.2) hzeta
  refine ⟨?_, ?_, zero_symmetries_commute Z⟩
  · constructor
    · intro hcritical n
      exact (mirror_index_fixed_iff_critical Z n).2 (hcritical n)
    · intro hfixed n
      exact (mirror_index_fixed_iff_critical Z n).1 (hfixed n)
  · intro hoff
    push Not at hoff
    obtain ⟨n, hn⟩ := hoff
    exact ⟨n, zero_orbit_card_four_of_off_line Z n (hconjugation n) hn⟩

#print axioms critical_line_stabilizer_orbit_dichotomy

end D5.S3.Zeros.Symmetry.CriticalLineStabilizerOrbit

/- GID: D5/S3/Zeros/Symmetry/ZeroOrbitDegeneracy
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Count zero-symmetry orbit cardinalities: two for non-self-conjugate critical zeros, two for self-conjugate off-critical zeros, and one for self-conjugate critical zeros. -/

import D5.S3.Zeros.Symmetry.ZeroOrbitCardinality

/- Provenance: Native proof over pinned mathlib. -/

/-!
SEARCH RECEIPT (2026-08-17):
* `D5/S3/Zeros/Symmetry/ZeroOrbitCardinality.lean:17-71` supplies the
  four-point template and its local distinctness arguments.
* `D5/S3/Zeros/Symmetry/ZeroSymmetryAction.lean:19-55` supplies commutation
  and `mirror_index_fixed_iff_critical`.  `D5/S3/Weil/Convention.lean:42`
  defines `criticalAbscissa`; `D5/S3/Weil/ZeroSum.lean:72-85,123-137`
  supplies `ZeroData`, its fields, and both involutions.  Thus the equivalence
  `Z.reflection n = Z.conjugation n ↔ (Z.zero n).re = criticalAbscissa` is an
  immediate corollary; no existing declaration with that statement was found,
  so it remains private below.
* `D5/S3/Zeros/Symmetry/ReflectionFixedPointContrast.lean:23-44` already
  proves the related complex-level fixed-locus contrast; it is not reproved.
* `D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits.lean:59-123`
  manipulates the same four-element `Finset`; no degenerate-cardinality result
  occurs there.
* Pinned Mathlib's `Mathlib/Data/Finset/Card.lean:138-143` supplies
  `Finset.card_pair`, used for the two-point computations.
* Repository and pinned-Mathlib searches for real/self-conjugate nontrivial
  zeros and zeta nonvanishing on `0 < re < 1` found no exclusion theorem.  The
  pinned nonvanishing results located are `riemannZeta_ne_zero_of_one_lt_re` at
  `Mathlib/NumberTheory/LSeries/Dirichlet.lean:325-327` and the stronger
  `riemannZeta_ne_zero_of_one_le_re` at
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:410-413`.  Between them they
  cover at most `1 <= re`, so neither yields a vacuity proof for the
  self-conjugate hypotheses of Layers 2-3, which live in `0 < re < 1`.
-/

namespace D5.S3.Zeros.Symmetry.ZeroOrbitDegeneracy

open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open D5.S3.Zeros.Symmetry.ZeroSymmetryAction

private theorem reflection_eq_conjugation_iff_critical (Z : ZeroData) (n : ℕ) :
    Z.reflection n = Z.conjugation n ↔
      (Z.zero n).re = criticalAbscissa := by
  constructor
  · intro h
    apply (mirror_index_fixed_iff_critical Z n).1
    simpa using congrArg Z.conjugation h
  · intro h
    have hM := (mirror_index_fixed_iff_critical Z n).2 h
    simpa using congrArg Z.conjugation hM

/-- On the critical line, a non-self-conjugate zero has a two-point orbit. -/
theorem zero_orbit_card_two_of_critical (Z : ZeroData) (n : ℕ)
    (hC : Z.conjugation n ≠ n) (hOn : (Z.zero n).re = criticalAbscissa) :
    ({n, Z.reflection n, Z.conjugation n,
      Z.conjugation (Z.reflection n)} : Finset ℕ).card = 2 := by
  have hRC := (reflection_eq_conjugation_iff_critical Z n).2 hOn
  have hM := (mirror_index_fixed_iff_critical Z n).2 hOn
  simpa [hRC, hM] using Finset.card_pair hC

/-- Off the critical line, a self-conjugate zero has a two-point orbit. -/
theorem zero_orbit_card_two_of_real (Z : ZeroData) (n : ℕ)
    (hC : Z.conjugation n = n) (hOff : (Z.zero n).re ≠ criticalAbscissa) :
    ({n, Z.reflection n, Z.conjugation n,
      Z.conjugation (Z.reflection n)} : Finset ℕ).card = 2 := by
  have hR : Z.reflection n ≠ n := by
    intro h
    apply hOff
    apply (mirror_index_fixed_iff_critical Z n).1
    simp [h, hC]
  have hM : Z.conjugation (Z.reflection n) = Z.reflection n := by
    calc
      Z.conjugation (Z.reflection n) = Z.reflection (Z.conjugation n) :=
        (zero_symmetries_commute Z n).symm
      _ = Z.reflection n := congrArg Z.reflection hC
  simpa [hC, hM] using Finset.card_pair hR.symm

/-- A critical, self-conjugate zero has a singleton orbit. -/
theorem zero_orbit_card_one_of_critical_real (Z : ZeroData) (n : ℕ)
    (hC : Z.conjugation n = n) (hOn : (Z.zero n).re = criticalAbscissa) :
    ({n, Z.reflection n, Z.conjugation n,
      Z.conjugation (Z.reflection n)} : Finset ℕ).card = 1 := by
  have hRC := (reflection_eq_conjugation_iff_critical Z n).2 hOn
  have hR : Z.reflection n = n := hRC.trans hC
  simp [hC, hR]

#print axioms zero_orbit_card_two_of_critical
#print axioms zero_orbit_card_two_of_real
#print axioms zero_orbit_card_one_of_critical_real

end D5.S3.Zeros.Symmetry.ZeroOrbitDegeneracy

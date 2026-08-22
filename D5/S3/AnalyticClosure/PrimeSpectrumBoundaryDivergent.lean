/- GID: D5/S3/AnalyticClosure/PrimeSpectrumBoundaryDivergent
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Linear prime spectra diverge at their reciprocal heat boundary. -/

import Mathlib
import D5.S3.AnalyticClosure.PrimeSpectrumHeatAbscissa

/- Provenance: Native proof over pinned mathlib. -/

/- Search receipt (2026-08-21).

   Candidates searched and inspected:
   * Listed all files directly in `D5/S3/AnalyticClosure` and
     `D5/S3/Midline`, then searched those directories recursively for
     `BoundaryDivergentAbscissa`, `IsHeatAbscissa`, and the cited theorem
     names. The relevant declarations were read in
     `PrimeSpectrumHeatAbscissa.lean`, `GoldenHeatBoundary.lean`,
     `UniversalHeatTrace.lean`, and `GoldenHeatLayers.lean`; the golden boundary
     proof was read in full. `GoldenHeatLayers.lean` proves a boundary-divergent
     abscissa for each golden layer and is ruled out here because it fixes the
     golden exponent family rather than an abstract linear-growth sequence.
   * Enumerated all subdirectories of pinned `Mathlib/NumberTheory`, then
     searched the eight files in that tree which mention `Nat.Primes` for
     reciprocal-series summability and divergence. This located
     `Mathlib/NumberTheory/SumPrimeReciprocals.lean`, whose two divergence
     formulations and prime-power summability criterion were inspected.
   * SL-028 was checked in a run-local scratch file with different declaration,
     binder, and helper names but the same statement shape. Repository searches
     also covered the name fragments `PrimeSpectrumBoundaryDivergent` and
     `prime_spectrum_boundary_divergent`; no declaration with this result was
     found.
   * In that scratch file, `decide`, `simp`, `omega`, and `norm_num` did not
     close the statement. The shortest one-lemma probe
     `simp [Nat.Primes.not_summable_one_div]` also did not close it and reported
     the supplied lemma unused.

   Load-bearing declarations and tactics:
   * `prime_spectrum_heat_abscissa` supplies the first conjunct under exactly
     the three hypotheses below.
   * `Equiv.prodComm.summable_iff` reindexes a hypothetical boundary sum and
     `Summable.prod_factor` restricts it to the zero layer.
   * `Real.exp_neg` and `Real.exp_log` turn the zero-layer exponential into a
     reciprocal after `rw [h1]`; `field_simp [ne_of_gt h0]` proves the exponent
     identity, and `exact_mod_cast p.prop.pos` supplies positivity of the prime.
   * `simp only [one_div]` closes the helper by putting the inverse into
     reciprocal form, and `Summable.congr` transports summability along that
     helper from the exponential family to the prime-reciprocal family.
   * `Nat.Primes.not_summable_one_div` contradicts summability of the resulting
     prime-reciprocal family.
   * Source inspection found no `@[simp]` attribute on these load-bearing
     declarations. The zero-layer numeral reductions are simplifier-supported
     but do not discharge any mathematical obligation.

   Thin-wrapper pre-screen: no single existing declaration, including the
   divergence theorem under the one-lemma simp probe above, closes the result.
   The proof additionally needs restriction to a subfamily and the computation
   that `-(1 / b0) * beta 1 = -1`. The inspected-candidate and load-bearing
   lists are separate and are not claimed exhaustive. -/

namespace D5.S3.AnalyticClosure.PrimeSpectrumBoundaryDivergent

open D5.S3.AnalyticClosure.PrimeSpectrumHeatAbscissa
open D5.S3.Midline.UniversalHeatTrace

noncomputable section

private theorem prime_boundary_term (beta : Nat → Real) (b0 : Real)
    (h0 : 0 < b0) (h1 : beta 1 = b0) (p : Nat.Primes) :
    Real.exp (-(1 / b0) * (beta 1 * Real.log (p : Real))) =
      (1 / p : Real) := by
  have hp : 0 < (p : Real) := by
    exact_mod_cast p.prop.pos
  rw [h1]
  rw [show -(1 / b0) * (b0 * Real.log (p : Real)) =
      -Real.log (p : Real) by field_simp [ne_of_gt h0]]
  rw [Real.exp_neg, Real.exp_log hp]
  simp only [one_div]

/-- A prime-by-natural spectrum with the general linear-growth heat abscissa
diverges at the boundary because its zero layer is the prime reciprocal series. -/
theorem prime_spectrum_boundary_divergent (beta : Nat → Real) (b0 : Real)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : Real) ≤ beta (k + 1)) :
    BoundaryDivergentAbscissa
      (fun pk : Nat.Primes × Nat =>
        beta (pk.2 + 1) * Real.log (pk.1 : Real))
      (1 / b0) := by
  constructor
  · exact prime_spectrum_heat_abscissa beta b0 h0 h1 h2
  · intro hsum
    have hswapped : Summable (fun kp : Nat × Nat.Primes =>
        Real.exp (-(1 / b0) *
          (beta (kp.1 + 1) * Real.log (kp.2 : Real)))) :=
      (Equiv.prodComm Nat.Primes Nat).summable_iff.mp hsum
    have hsub : Summable (fun p : Nat.Primes =>
        Real.exp (-(1 / b0) * (beta 1 * Real.log (p : Real)))) :=
      hswapped.prod_factor 0
    have hrecip : Summable (fun p : Nat.Primes => (1 / p : Real)) := by
      exact hsub.congr fun p => prime_boundary_term beta b0 h0 h1 p
    exact Nat.Primes.not_summable_one_div hrecip

#print axioms prime_spectrum_boundary_divergent

end

end D5.S3.AnalyticClosure.PrimeSpectrumBoundaryDivergent

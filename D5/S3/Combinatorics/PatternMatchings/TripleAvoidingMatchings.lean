/- GID: D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings
   mirror-E: none(waiver:biswas-shankar-sivasubramanian-p1-enumeration)
   anchors: []
   utility: none
   digest: The Catalan-Fibonacci series enumerates P1-avoiding matchings at every size. -/

import D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchingsBulk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings

open TripleAvoidingMatchingsDefs PowerSeries

/-- The P1 clause of Biswas--Shankar--Sivasubramanian, Section 6, Question 1. -/
theorem result : TripleAvoidingMatchingsDefs.claim := by
  obtain ⟨h0, h1, _, _, _, _, hmatch⟩ := word_series_recursion
  rw [bulk_enumeration] at h1
  have hs : (1 - X ^ 2 - X ^ 2 * expand 2 (by decide) hSeries) *
      wordSeries 0 false = 1 - X ^ 2 * expand 2 (by decide) hSeries := by
    linear_combination
      (1 - X ^ 2 * expand 2 (by decide) hSeries) * h0 + X * h1
  have hex : expand 2 (by decide) ((1 - X - X * hSeries) * aSeries) =
      expand 2 (by decide) (1 - X * hSeries) := by
    simpa only [map_mul, map_sub, map_one, expand_X, hmatch] using hs
  unfold TripleAvoidingMatchingsDefs.claim
  apply PowerSeries.ext
  intro n
  have hc := congrArg (coeff (2 * n)) hex
  simpa only [coeff_expand_mul] using hc

end D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings

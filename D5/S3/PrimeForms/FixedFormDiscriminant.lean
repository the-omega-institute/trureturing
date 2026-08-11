/- GID: D5/S3/PrimeForms/FixedFormDiscriminant
   generality: G
   mirror-B: D5/B/S3/PrimeForms/FixedFormDiscriminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The discriminant of the fixed-point quadratic form of a 2×2 integer matrix equals tr²−4·det; for determinant −1 it is tr²+4, and for the pinned odd core of trace 12j it is 4(36j²+1), exactly four times the negative-Pell discriminant. -/

import Mathlib

namespace D5.S3.PrimeForms.FixedFormDiscriminant

/-- The discriminant of the fixed-point quadratic form of a 2×2 integer matrix
`[[a, b], [c, d]]`: the fixed-point equation `x = (ax+b)/(cx+d)` has quadratic
`c·x² + (d−a)·x − b`, whose discriminant is `(d−a)² + 4bc`. -/
def fixedFormDiscriminant (a b c d : ℤ) : ℤ := (d - a) ^ 2 + 4 * b * c

/-- The fixed-form discriminant equals `tr² − 4·det`. -/
theorem fixedFormDiscriminant_eq (a b c d : ℤ) :
    fixedFormDiscriminant a b c d = (a + d) ^ 2 - 4 * (a * d - b * c) := by
  unfold fixedFormDiscriminant; ring

/-- Core discriminant lemma (E.53): for a matrix of determinant `−1`, the fixed-form
discriminant is `tr² + 4`. -/
theorem det_neg_one_fixed_form_disc (a b c d : ℤ) (h : a * d - b * c = -1) :
    fixedFormDiscriminant a b c d = (a + d) ^ 2 + 4 := by
  rw [fixedFormDiscriminant_eq, h]; ring

/-- Pinned odd core (trace `12j`, determinant `−1`): the fixed-form discriminant is
`4·(36j² + 1)`, exactly four times the negative-Pell discriminant `d_j = 36j² + 1`. -/
theorem pinned_core_disc (a b c d j : ℤ) (h : a * d - b * c = -1) (htr : a + d = 12 * j) :
    fixedFormDiscriminant a b c d = 4 * (36 * j ^ 2 + 1) := by
  rw [det_neg_one_fixed_form_disc a b c d h, htr]; ring

end D5.S3.PrimeForms.FixedFormDiscriminant

/- GID: D5/S3/Arith/AbsoluteValues/OstrowskiClassification
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/OstrowskiClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every nontrivial real-valued absolute value on Q is real or uniquely p-adic. -/

import Mathlib.NumberTheory.Ostrowski

/- Library-search audit trail (2026-08-17):
   * Pinned-mathlib search found the exact classification theorem
     `Rat.AbsoluteValue.equiv_real_or_padic` in `Mathlib.NumberTheory.Ostrowski`.
   * Loogle found the same single declaration. LeanSearch's `/api/search` returned 404, and
     unauthenticated GitHub code search returned 401.
   * Repository searches for Ostrowski and equivalent rational-absolute-value classifications
     found no declaration in `D5/` or `Blueprint/`.
-/

namespace D5.S3.Arith.AbsoluteValues.OstrowskiClassification

/-- **Ostrowski classification for the rationals.** Every nontrivial real-valued absolute value
on `Q` is equivalent either to the standard absolute value or to the `p`-adic absolute value for
a unique prime `p`. -/
theorem rational_absolute_value_classification
    (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    f ≈ Rat.AbsoluteValue.real ∨
      ∃! p : ℕ, ∃ (_ : Fact p.Prime), f ≈ Rat.AbsoluteValue.padic p :=
  Rat.AbsoluteValue.equiv_real_or_padic f hf

#print axioms rational_absolute_value_classification

end D5.S3.Arith.AbsoluteValues.OstrowskiClassification

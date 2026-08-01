/- GID: D5/S3/Analytic/LedgerLengthGrowth
   generality: I
   mirror-B: D5/B/S3/Analytic/LedgerLengthGrowth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive ledger generation strictly increases every additive real length. -/

import D5.S3.Weil.LabeledZeta

namespace D5.S3.Analytic.LedgerLengthGrowth

open D5.S3.Weil.LabeledZeta

/-- Adding a generation of positive length strictly increases ledger length. -/
theorem ledger_length_strict_mono_of_positive_generation {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (a u : A) (hu : 0 < length u) :
    length a < length (a + u) := by
  rw [map_add]
  exact lt_add_of_pos_right _ hu

end D5.S3.Analytic.LedgerLengthGrowth

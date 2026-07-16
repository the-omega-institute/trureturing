/- GID: D5/S3/Weil/LabeledZeta
   generality: I
   mirror-B: D5/B/S3/Weil/LabeledZeta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A labeled heat-trace vector has unit empty-ledger coordinate and is never zero. -/

import D5.S3.Weil.Convention

namespace D5.S3.Weil.LabeledZeta

/-- An additive real length on a ledger monoid. -/
abbrev LedgerLength (A : Type*) [AddMonoid A] := A →+ ℝ

/-- The coordinatewise labeled heat-trace vector; no summability is required. -/
noncomputable def labeledZeta {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (s : ℂ) : A → ℂ :=
  fun a ↦ Complex.exp (-s * (length a : ℂ))

/-- The empty-ledger coordinate is one, so the labeled vector cannot vanish. -/
theorem labeled_zeta_vector_ne_zero {A : Type*} [AddMonoid A]
    (length : LedgerLength A) (s : ℂ) : labeledZeta length s ≠ 0 := by
  intro hzero
  have hcoordinate := congr_fun hzero (0 : A)
  simp [labeledZeta] at hcoordinate

end D5.S3.Weil.LabeledZeta

/- GID: D5/S0/Diagonal/Naturality/QuotientTwistBlindness
   generality: G
   mirror-B: D5/B/S0/Diagonal/Naturality/QuotientTwistBlindness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A value interface invariant under a twist cannot detect that twist on diagonals. -/

import D5.S0.Diagonal.Naturality.CoordinateRestrictionNaturality

/- Library-search audit trail (2026-08-15):
   * Loogle query `Function.Semiconj` found the exact composition characterization
     `Function.semiconj_iff_comp_eq` and its pointwise projection `Function.Semiconj.eq`.
   * LeanSearch query `a function semiconjugates one self-map to another exactly when the
     corresponding function compositions are equal` returned `Function.semiconj_iff_comp_eq`
     as its first result. The full-statement query `a map q satisfying q after tau equals q makes
     the twisted diagonal observationally equal to the ordinary diagonal` found only unrelated
     diagonal-map declarations and no theorem about twisted listing diagonals.
   * Pinned-Mathlib grep confirmed those declarations in `Mathlib.Logic.Function.Conjugate` and
     found no full-statement match. Repository search found the exact stronger support theorem
     `coordinate_restriction_naturality`, imported and applied below, but no duplicate of this
     identity-coarse-twist specialization. -/

namespace D5.S0.Diagonal.Naturality.QuotientTwistBlindness

open D5.S0.Diagonal
open D5.S0.Diagonal.Naturality.CoordinateRestrictionNaturality

/-- If a value interface identifies every value with its twisted value, then it gives the same
observable vector on the twisted and untwisted diagonals of every self-application table. -/
theorem quotient_twist_blindness
    {A Y Z : Type*} (q : Y -> Z) (tau : Y -> Y)
    (hhidden : q ∘ tau = q) (E : A -> A -> Y) :
    q ∘ EscapeCount.diagonal tau E = q ∘ EscapeCount.diagonal id E := by
  have hsemiconj : Function.Semiconj q tau id :=
    Function.semiconj_iff_comp_eq.mpr (by simpa using hhidden)
  have h := coordinate_restriction_naturality
    (iota := Function.Embedding.refl A) q tau id hsemiconj.comp_eq E
  change (fun a => q (tau (E a a))) = (fun a => q (E a a)) at h
  exact h

end D5.S0.Diagonal.Naturality.QuotientTwistBlindness

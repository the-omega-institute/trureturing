/- GID: D5/S3/Observer/ConditioningCertificate
   generality: G
   mirror-B: D5/B/S3/Observer/ConditioningCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify exact finite record conditioning by a vanishing matrix defect. -/

/- Library-search audit trail (2026-08-09):
   * Local mathlib searches for subtraction-to-zero identities found `sub_eq_zero`; the proof
     reuses `sub_eq_zero.mpr` rather than reproving the additive-group equivalence.
   * The conditioning-specific equality is reused from
     `D5.S3.Observer.Conditioning.unread_eq_weighted_ensemble`.
-/

import D5.S3.Observer.Conditioning

namespace D5.S3.Observer.ConditioningCertificate

open D5.S3.Observer.Conditioning
open scoped BigOperators ComplexOrder

variable {n kappa : Type*} [Fintype n] [DecidableEq n]
    [Fintype kappa]
    {P : kappa -> Matrix n n ℂ}

/-- The matrix residual between unread conditioning and its weighted conditional ensemble. -/
noncomputable def conditioningDefect (P : kappa -> Matrix n n ℂ)
    (rho : Matrix n n ℂ) : Matrix n n ℂ :=
  unreadState P rho - ∑ k, recordWeight P rho k • conditionalState P rho k

/-- Exact conditioning has zero matrix-valued certificate defect, with no tolerance term. -/
theorem certificate_identity_zero_tolerance (hP : IsRecordMeasurement P)
    {rho : Matrix n n ℂ} (hRho : rho.PosSemidef) :
    conditioningDefect P rho = 0 := by
  unfold conditioningDefect
  exact sub_eq_zero.mpr (unread_eq_weighted_ensemble hP hRho)

end D5.S3.Observer.ConditioningCertificate

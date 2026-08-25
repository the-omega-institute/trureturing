/- GID: D5/S3/Factorization/IdealClassGroups/PrincipalIdealCriterion
   generality: G
   mirror-B: D5/B/S3/Factorization/IdealClassGroups/PrincipalIdealCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An invertible fractional ideal is principal exactly when its ideal class is trivial. -/
/- Library-search audit trail (2026-08-25):
   * Lean LSP search commands were unavailable; `smart_search.sh` and repository `rg`
     searches found no repository declaration of this criterion.
   * Pinned Mathlib's `ClassGroup.mk_eq_one_iff` is the exact principal-class criterion. -/

import Mathlib.RingTheory.ClassGroup.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.IdealClassGroups.PrincipalIdealCriterion

open scoped nonZeroDivisors

universe u v

/- `CommRing R` and `IsDomain R` form `ClassGroup R`; `Field K`, `Algebra R K`, and
`IsFractionRing R K` let its class map use `K`. These are exactly the five instances required by
`ClassGroup.mk_eq_one_iff`; no Dedekind-domain instance is used. -/
/-- An invertible fractional ideal is principal exactly when its ideal class is trivial. -/
theorem principal_ideal_criterion
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {I : (FractionalIdeal R⁰ K)ˣ} :
    (I : Submodule R K).IsPrincipal ↔ ClassGroup.mk K I = 1 := by
  exact ClassGroup.mk_eq_one_iff.symm
#print axioms principal_ideal_criterion

end D5.S3.Factorization.IdealClassGroups.PrincipalIdealCriterion

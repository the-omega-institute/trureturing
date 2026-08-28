/- GID: D5/S3/ConceptDynamics/Dialectics/RealizedReadoutCompatibility
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Dialectics/RealizedReadoutCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The realized readout is Mathlib's canonical factorization through a range. -/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
import Mathlib.Data.Set.Operations

/- Library-search audit trail (2026-08-28):
   * The repository search followed the realized-image construction, not a guessed theorem
     name. No file mentioned both `realizedReadout` and `Set.rangeFactorization`, so no bridge
     related the two definitions before this module.
   * The pinned Mathlib source at revision `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
     defines `Set.rangeFactorization f` as `fun i => ⟨f i, Set.mem_range_self i⟩`.
     Loogle independently returned that exact declaration in `Mathlib.Data.Set.Operations`,
     followed by `Set.rangeFactorization_surjective`; the exact definition is used directly.
   * LeanSearch's HTML page was reachable, but its attempted JSON API endpoint returned 404,
     so no LeanSearch result is claimed. No local proof beyond definitional equality remains. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Dialectics.RealizedReadoutCompatibility

open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence

/-- The locally defined realized readout is Mathlib's canonical factorization of a function
through its range.

**What this does not claim.** The equality does not say that `q` is injective or surjective
onto its original codomain `B`, nor does it identify `B` with `Set.range q`. It introduces no
quotient or coercion: both sides have exactly the existing codomain `Set.range q`. Mathlib's
separate theorem `Set.rangeFactorization_surjective` says only that this common map is
surjective onto that realized range. -/
theorem realizedReadout_eq_rangeFactorization
    {X B : Type*} (q : X → B) :
    realizedReadout q = Set.rangeFactorization q := by
  rfl

/-- Reverse probe for CAS-B1: the public function equality controls every source point. -/
example
    {X B : Type*} (q : X → B)
    (bridge : realizedReadout q = Set.rangeFactorization q) (x : X) :
    realizedReadout q x = Set.rangeFactorization q x :=
  congrFun bridge x

#print axioms realizedReadout_eq_rangeFactorization

end D5.S3.ConceptDynamics.Dialectics.RealizedReadoutCompatibility

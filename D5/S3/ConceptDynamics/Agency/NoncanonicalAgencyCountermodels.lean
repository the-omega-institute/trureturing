/- GID: D5/S3/ConceptDynamics/Agency/NoncanonicalAgencyCountermodels
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Agency/NoncanonicalAgencyCountermodels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fair and reason-sensitive choices separate authorship from canonicity. -/

import D5.S3.ConceptDynamics.Agency.SelfFormationFreeWillBoundary
import Mathlib.Probability.Distributions.Uniform

/- Library-search audit trail (2026-08-27):
   * No repository theorem packages both Boolean countermodels. The existing
     symmetric-tie theorem has no stochastic law or internal-reason clause,
     while the existing deterministic-autonomy model lacks a public clause
     making distinct internal reasons select distinct actions.
   * Exact family hit `FunctionalFuture` supplies the canonical deterministic
     process predicate and is imported rather than restated.
   * Exact pinned-Mathlib hits `PMF.uniformOfFintype`,
     `PMF.uniformOfFintype_apply`, and `Bool.not_ne_self` construct the fair law
     and exclude a deterministic selector invariant under candidate exchange.
     No packaged theorem supplies both models. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Agency.NoncanonicalAgencyCountermodels

open D5.S3.ConceptDynamics.Agency.SelfFormationFreeWillBoundary

/-- Two Boolean countermodels separate deterministic canonicity from internal
authorship. A fair tie law is independent of the internal reason and admits no
deterministic selector invariant under its candidate-exchange symmetry.
Conversely, a functionally deterministic process can select distinct actions
from distinct internal reasons while the external setting is held fixed. -/
theorem noncanonical_and_deterministic_agency_countermodels :
    (exists tieLaw : Bool -> PMF Bool,
    (forall reason action, tieLaw reason action = (2 : ENNReal)⁻¹) /\
        (forall leftReason rightReason, tieLaw leftReason = tieLaw rightReason) /\
        Not (exists selector : Bool -> Bool,
          forall reason,
            (forall action,
              tieLaw reason (Bool.not action) = tieLaw reason action) ->
            Bool.not (selector reason) = selector reason)) /\
      (exists process : Bool -> Bool -> Set Bool,
        (forall external, FunctionalFuture (process external)) /\
          exists external reason₁ reason₂ action₁ action₂,
            reason₁ ≠ reason₂ /\
              process external reason₁ = {action₁} /\
              process external reason₂ = {action₂} /\
              action₁ ≠ action₂) := by
  constructor
  · refine ⟨fun _ => PMF.uniformOfFintype Bool, ?_, ?_, ?_⟩
    · intro reason action
      norm_num [PMF.uniformOfFintype_apply, Fintype.card_bool]
    · intro leftReason rightReason
      rfl
    · rintro ⟨selector, canonical⟩
      have fixedPoint := canonical false (by
        intro action
        simp only [PMF.uniformOfFintype_apply])
      exact Bool.not_ne_self (selector false) fixedPoint
  · refine ⟨fun _ reason => {reason}, ?_, ?_⟩
    · intro external
      exact ⟨id, fun reason => rfl⟩
    · exact ⟨false, false, true, false, true,
        Bool.false_ne_true, rfl, rfl, Bool.false_ne_true⟩

#print axioms noncanonical_and_deterministic_agency_countermodels

end D5.S3.ConceptDynamics.Agency.NoncanonicalAgencyCountermodels

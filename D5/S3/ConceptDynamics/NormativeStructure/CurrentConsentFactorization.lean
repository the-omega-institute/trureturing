/- GID: D5/S3/ConceptDynamics/NormativeStructure/CurrentConsentFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/NormativeStructure/CurrentConsentFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Non-factorization of current consent rules out exact systems using only history. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-25):
   * `rg -n -i 'consent|withdraw|history.*factor|current.*factor' D5/S3/ConceptDynamics --glob '*.lean'`
     found no exact current-consent obstruction theorem.
   * The nearest frozen factorization result is
     `history_sensitive_evaluation_not_outcome_reducible`; it handles equal
     endpoint fibers with unequal evaluations, but does not expose the source's
     current-consent premise and exact-response equality, so it is not an exact hit.
   * The canonical `Concept` carrier and source factorization relation
     `ConceptJoinUniversal.Refines` are imported directly; no sibling readout
     type or factorization relation is introduced.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.NormativeStructure.CurrentConsentFactorization

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/- If current consent is not a function of history, no history-only system can
   equal it exactly. -/
theorem current_consent_not_history_only
    {X History : Type*}
    (history : Concept X History) (currentConsent : Concept X Bool)
    (notFactor : ¬ Refines currentConsent history) :
    ¬ ∃ system : Concept X Bool,
        Refines system history ∧ system = currentConsent := by
  rintro ⟨system, systemFactors, exactResponse⟩
  apply notFactor
  rcases systemFactors with ⟨factor, factorization⟩
  exact ⟨factor, exactResponse.symm.trans factorization⟩

example :
    ¬ Refines (id : Concept Bool Bool) (fun _ : Bool => ()) ∧
      ¬ ∃ system : Concept Bool Bool,
        Refines system (fun _ : Bool => ()) ∧
          system = id := by
  constructor
  · intro factors
    rcases factors with ⟨factor, factorization⟩
    have falseEqualsTrue := congrFun factorization false |>.trans
      (congrFun factorization true).symm
    exact Bool.false_ne_true falseEqualsTrue
  · exact current_consent_not_history_only
      (fun _ : Bool => ()) id (by
        intro factors
        rcases factors with ⟨factor, factorization⟩
        have falseEqualsTrue := congrFun factorization false |>.trans
          (congrFun factorization true).symm
        exact Bool.false_ne_true falseEqualsTrue)

#print axioms current_consent_not_history_only

end D5.S3.ConceptDynamics.NormativeStructure.CurrentConsentFactorization

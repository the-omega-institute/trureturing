/- GID: D5/S3/Observer/HiddenFlow/SupportExternalMechanism
   generality: G
   mirror-B: D5/B/S3/Observer/HiddenFlow/SupportExternalMechanism
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A support-restricted observation channel leaves hidden mechanism values unidentified. -/

import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-24):
   * `rg` over `D5/S3/Observer` and `D5/S3/ConceptDynamics` found no exact
     support-restriction channel theorem for a mechanism changed outside its
     accessed parent support.
   * `EmpiricalIdentifiability.empirical_identifiability` is an adjacent exact
     fiber criterion and was inspected, but it quantifies over protocol outcomes
     rather than exposing the source's support-restricted channel.
   * `ObservationInterventionSeparation.observation_strictly_weaker_than_intervention`
     supplies a Boolean causal countermodel with a different intervention shape,
     so it is not a duplicate of this support-restriction statement.
   * Pinned Mathlib searches found only ordinary `Set` membership, subtype
     functions, `Function.funext`, and `exists_pair_ne`; no packaged theorem for
     this source mechanism was found. `loogle` and `leansearch` are absent.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.HiddenFlow.SupportExternalMechanism

/-- The channel exposed by a regime that accesses only a support of parent states. -/
def observationChannel {Parent Outcome : Type*}
    (support : Set Parent) (mechanism : Parent → Outcome) :
    {parent : Parent // parent ∈ support} → Outcome :=
  fun parent => mechanism parent.1

/-- A parent configuration outside the regime's support can carry a changed
mechanism value while the support-restricted observation channel is unchanged. -/
theorem unseen_parent_config_can_change_without_observed_law
    {Parent Outcome : Type*} [Nontrivial Outcome]
    (support : Set Parent) (hidden : Parent) (hhidden : hidden ∉ support) :
    ∃ mechanism₀ mechanism₁ : Parent → Outcome,
      observationChannel support mechanism₀ = observationChannel support mechanism₁ ∧
        mechanism₀ hidden ≠ mechanism₁ hidden := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne Outcome
  refine ⟨fun _ => a, fun parent => if parent = hidden then b else a, ?_, ?_⟩
  · funext parent
    have hne : (parent : Parent) ≠ hidden := by
      intro hEq
      exact hhidden (hEq ▸ parent.property)
    simp [observationChannel, hne]
  · simpa using hab

/-- Boolean values give an inhabited concrete model of the hidden-configuration
counterexample. -/
theorem boolean_hidden_parent_countermodel :
    ∃ mechanism₀ mechanism₁ : Bool → Bool,
        observationChannel ({false} : Set Bool) mechanism₀ =
          observationChannel ({false} : Set Bool) mechanism₁ ∧
        mechanism₀ true ≠ mechanism₁ true := by
  classical
  exact unseen_parent_config_can_change_without_observed_law
    ({false} : Set Bool) true (by
      intro h
      change true = false at h
      cases h)

#print axioms unseen_parent_config_can_change_without_observed_law

end D5.S3.Observer.HiddenFlow.SupportExternalMechanism

/- GID: D5/S3/ConceptDynamics/ExperimentBoundary/FiniteIdentificationOutputCapacity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentBoundary/FiniteIdentificationOutputCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite protocol separation has effective-output capacity bounds. -/

import D5.S3.ConceptDynamics.Experiment.FiniteIdentificationCapacityBound
import D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
import Mathlib.Data.Fintype.BigOperators

/- Library-search audit trail (2026-08-28):
   * Exact family hit `jointReadout` is the canonical dependent protocol bundle
     and is imported rather than redeclared.
   * `FiniteIdentificationCapacityBound` proves only the full-output-space
     cardinal and base-two bounds; it does not count each protocol's effective
     image or prove the uniform-output protocol lower bound.
   * Exact pinned-Mathlib component hits `Nat.card_le_card_of_injective`,
     `Nat.card_pi`, `Real.log_prod`, `Real.logb_le_logb`, `Real.logb_pow`, and
     `Nat.ceil_le` are applied below. No exact packaged theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ExperimentBoundary.FiniteIdentificationOutputCapacity

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion

universe u v w

/-- A finite family separating a nonempty finite state-class carrier has enough
effective joint outputs. Consequently its base-two information is sufficient;
if every effective output count is at most `bound > 1`, the family cardinality
is at least the ceiling of the base-`bound` logarithm of the state count. -/
theorem finite_identification_output_capacity
    {X : Type u} {Protocol : Type v} [Finite X] [Nonempty X]
    [Fintype Protocol] {Output : Protocol → Type w}
    (readout : (protocol : Protocol) → X → Output protocol)
    (separates : Function.Injective (jointReadout readout)) :
    let stateCount := Nat.card X
    let outputCount := fun protocol => Nat.card (Set.range (readout protocol))
    stateCount ≤ ∏ protocol, outputCount protocol ∧
      Real.logb 2 stateCount ≤
        ∑ protocol, Real.logb 2 (outputCount protocol) ∧
      ∀ bound : Nat, 1 < bound →
        (∀ protocol, outputCount protocol ≤ bound) →
        ⌈Real.logb bound stateCount⌉₊ ≤ Fintype.card Protocol := by
  dsimp only
  let effectiveJoint : X →
      ((protocol : Protocol) → Set.range (readout protocol)) :=
    fun state protocol => ⟨readout protocol state, state, rfl⟩
  have effectiveJointInjective : Function.Injective effectiveJoint := by
    intro left right sameEffectiveOutputs
    apply separates
    funext protocol
    exact congrArg Subtype.val (congrFun sameEffectiveOutputs protocol)
  have cardinalBound :
      Nat.card X ≤ ∏ protocol, Nat.card (Set.range (readout protocol)) := by
    have embeddingBound :=
      Nat.card_le_card_of_injective effectiveJoint effectiveJointInjective
    simpa only [Nat.card_pi] using embeddingBound
  have outputCountPositive :
      ∀ protocol, 0 < Nat.card (Set.range (readout protocol)) := by
    intro protocol
    apply Finite.card_pos_iff.mpr
    let state := Classical.choice (inferInstance : Nonempty X)
    exact ⟨⟨readout protocol state, state, rfl⟩⟩
  have stateCountPositive : 0 < Nat.card X := Nat.card_pos
  constructor
  · exact cardinalBound
  constructor
  · have productPositive :
        0 < ∏ protocol, Nat.card (Set.range (readout protocol)) :=
      Finset.prod_pos fun protocol _ => outputCountPositive protocol
    have logarithmicBound :
        Real.logb 2 (Nat.card X) ≤
          Real.logb 2
            (∏ protocol, Nat.card (Set.range (readout protocol))) := by
      apply (Real.logb_le_logb (b := 2) (by norm_num)
        (by exact_mod_cast stateCountPositive)
        (by exact_mod_cast productPositive)).2
      exact_mod_cast cardinalBound
    calc
      Real.logb 2 (Nat.card X) ≤
          Real.logb 2
            (∏ protocol, Nat.card (Set.range (readout protocol))) :=
        logarithmicBound
      _ = ∑ protocol,
          Real.logb 2 (Nat.card (Set.range (readout protocol))) := by
        simp only [Real.logb]
        rw [Real.log_prod]
        · rw [Finset.sum_div]
        · intro protocol protocolInUniverse
          exact_mod_cast (outputCountPositive protocol).ne'
  · intro bound boundGreaterThanOne outputBound
    have productBound :
        (∏ protocol, Nat.card (Set.range (readout protocol))) ≤
          bound ^ Fintype.card Protocol := by
      calc
        (∏ protocol, Nat.card (Set.range (readout protocol))) ≤
            ∏ _protocol : Protocol, bound := by
          apply Finset.prod_le_prod
          · intro protocol protocolInUniverse
            exact Nat.zero_le _
          · intro protocol protocolInUniverse
            exact outputBound protocol
        _ = bound ^ Fintype.card Protocol := by simp
    have stateBound : Nat.card X ≤ bound ^ Fintype.card Protocol :=
      cardinalBound.trans productBound
    rw [Nat.ceil_le]
    have boundRealGreaterThanOne : (1 : Real) < bound := by
      exact_mod_cast boundGreaterThanOne
    have powerPositive :
        (0 : Real) < (bound : Real) ^ Fintype.card Protocol :=
      pow_pos (zero_lt_one.trans boundRealGreaterThanOne) _
    calc
      Real.logb bound (Nat.card X) ≤
          Real.logb bound ((bound : Real) ^ Fintype.card Protocol) := by
        apply (Real.logb_le_logb boundRealGreaterThanOne
          (by exact_mod_cast stateCountPositive) powerPositive).2
        exact_mod_cast stateBound
      _ = (Fintype.card Protocol : Real) := by
        rw [Real.logb_pow, Real.logb_self_eq_one boundRealGreaterThanOne]
        simp

#print axioms finite_identification_output_capacity

end D5.S3.ConceptDynamics.ExperimentBoundary.FiniteIdentificationOutputCapacity

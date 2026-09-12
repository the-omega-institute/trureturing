/- GID: D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.CommonSuccessPreservesDomains; result=D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.common_success_domain_refutation; claim=D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.CommonSuccessPreservesDomains
   digest: Jointly successful context readings can agree while partial definedness differs. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Observation.PartialFunctionDomainObservation

inductive State
  | a
  | b
  deriving DecidableEq

/-- A readout into the two-element set, with one unrealized value. -/
def q : State → Fin 2 := fun _ => 0

/-- The only operation fixes `a` and is undefined at `b`. -/
def partialRead : State → Option State
  | .a => some .a
  | .b => none

/-- All finite contexts for the signature with this one unary operation.
Zero is the identity hole. Bind propagates failure without feeding it to the operation. -/
def eval : Nat → State → Option State
  | 0, x => some x
  | n + 1, x => (eval n x).bind partialRead

/-- `some v` represents the tagged success `(1,v)`; `none` is the separate failure tag. -/
def observe (n : Nat) (x : State) : Option (Fin 2) := (eval n x).map q

/-- This comparison discards every context that fails on either input. -/
def commonSuccessAgreement (x y : State) : Prop :=
  ∀ (n : Nat) (u v : State), eval n x = some u → eval n y = some v → q u = q v

def partialDomain : Set State := {x | partialRead x ≠ none}

def qSaturated (S : Set State) : Prop :=
  ∀ (x y : State), q x = q y → (x ∈ S ↔ y ∈ S)

/-- The erroneous claim that common-success comparison preserves operation domains. -/
def CommonSuccessPreservesDomains : Prop :=
  ∀ (x y : State), commonSuccessAgreement x y →
    (x ∈ partialDomain ↔ y ∈ partialDomain)

private theorem context_evaluation (n : Nat) :
    eval n .a = some .a ∧ eval n .b = if n = 0 then some .b else none := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    constructor
    · simp [eval, ih.1, partialRead]
    · simp only [eval, ih.2, Nat.succ_ne_zero, if_false]
      split <;> rfl

/-- The exact observation profile covers arbitrary finite context depth. -/
theorem context_observation_profile (n : Nat) :
    observe n .a = some 0 ∧ observe n .b = if n = 0 then some 0 else none := by
  have h := context_evaluation n
  constructor
  · simp [observe, h.1, q]
  · simp only [observe, h.2]
    split <;> rfl

private theorem common_success_agreement : commonSuccessAgreement .a .b := by
  intro n u v _ _
  rfl

private theorem partial_domain_membership :
    State.a ∈ partialDomain ∧ State.b ∉ partialDomain := by
  simp [partialDomain, partialRead]

/-- Equal scalar readings do not make the partial domain a union of whole fibers. -/
theorem partial_domain_not_q_saturated : ¬ qSaturated partialDomain := by
  intro h
  exact partial_domain_membership.2 ((h .a .b rfl).mp partial_domain_membership.1)

/-- Common-success agreement does not preserve the definition domain. -/
theorem common_success_domain_refutation : ¬ CommonSuccessPreservesDomains := by
  intro h
  exact partial_domain_membership.2
    ((h .a .b common_success_agreement).mp partial_domain_membership.1)

/-- The complete two-state counterexample, including all finite contexts and zero-filled failure. -/
theorem partial_function_domain_counterexample :
    (∀ x : State, q x = 0) ∧
    ¬ Function.Surjective q ∧
    partialRead .a = some .a ∧ partialRead .b = none ∧
    partialDomain = {State.a} ∧
    commonSuccessAgreement .a .b ∧
    ¬ qSaturated partialDomain ∧
    ¬ CommonSuccessPreservesDomains ∧
    observe 1 .a = some 0 ∧ observe 1 .b = none ∧
    observe 1 .a ≠ observe 1 .b ∧
    (∀ n : Nat, (observe n .a).getD 0 = (observe n .b).getD 0) := by
  refine ⟨fun _ => rfl, ?_, rfl, rfl, ?_, common_success_agreement,
    partial_domain_not_q_saturated, common_success_domain_refutation, ?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨x, hx⟩ := h 1
    have hzero : (0 : Fin 2) = 1 := hx
    exact (by decide : (0 : Fin 2) ≠ 1) hzero
  · ext x
    change (partialRead x ≠ none) ↔ x = State.a
    cases x <;> simp [partialRead]
  · exact (context_observation_profile 1).1
  · simpa using (context_observation_profile 1).2
  · rw [(context_observation_profile 1).1]
    have hb : observe 1 .b = none := by simpa using (context_observation_profile 1).2
    rw [hb]
    intro h
    cases h
  · intro n
    rw [(context_observation_profile n).1, (context_observation_profile n).2]
    split <;> rfl

#print axioms context_observation_profile
#print axioms partial_domain_not_q_saturated
#print axioms common_success_domain_refutation
#print axioms partial_function_domain_counterexample

end D5.S3.ConceptDynamics.Observation.PartialFunctionDomainObservation

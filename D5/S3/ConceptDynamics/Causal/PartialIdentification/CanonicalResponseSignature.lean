/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/CanonicalResponseSignature
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/CanonicalResponseSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite total causal order yields finite predecessor-indexed deterministic response signatures whose event queries are exact linear objectives. -/

import D5.S0.Certificates.LinearObjectiveDual
import Mathlib.Data.Fintype.EquivFin

/- Library-search audit trail (2026-09-03):
   * `QueryOrderLinearExtension` supplies a complete order relation, while the
     existing structural semantics evaluates equations in a certified list.
   * Repository searches found no finite carrier collecting one deterministic
     predecessor-response table for every position in a total causal order.
   * `LinearObjectiveDual` already certifies arbitrary finite rational linear
     objectives. This module supplies the missing causal response-signature
     carrier and proves that Boolean signature events are such objectives. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.CanonicalResponseSignature

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual

universe u

/-- A total ordering of `n` named nodes, represented by the node occupying each
position. -/
abbrev FiniteNodeOrder (n : Nat) := Equiv.Perm (Fin n)

/-- The node occupying a specified position in a total causal order. -/
def nodeAt {n : Nat} (order : FiniteNodeOrder n) (position : Fin n) : Fin n :=
  order position

/-- Every named node occupies one and only one position in the total order. -/
theorem node_has_unique_position
    {n : Nat}
    (order : FiniteNodeOrder n)
    (node : Fin n) :
    exists unique position : Fin n, nodeAt order position = node := by
  refine ⟨order.symm node, ?_, ?_⟩
  · exact order.apply_symm_apply node
  · intro position position_eq
    apply order.injective
    simpa [nodeAt] using position_eq

/-- A canonical deterministic response signature indexed by total-order
positions. At position `j`, the structural response is a table from assignments
to the `j` predecessor positions to the current value. -/
structure CanonicalResponseSignature (n : Nat) (Value : Type u) where
  response : (position : Fin n) -> (Fin position.1 -> Value) -> Value

/-- The one-field response-signature structure is equivalent to its dependent
response table. -/
def responseTableEquiv
    (n : Nat) (Value : Type u) :
    CanonicalResponseSignature n Value ≃
      ((position : Fin n) -> (Fin position.1 -> Value) -> Value) where
  toFun := CanonicalResponseSignature.response
  invFun := fun response => ⟨response⟩
  left_inv := by
    intro signature
    cases signature
    rfl
  right_inv := by
    intro response
    rfl

/-- Finite node and value carriers produce a finite canonical response-signature
carrier, suitable for a response-type probability vector. -/
noncomputable instance canonicalResponseSignatureFintype
    (n : Nat) (Value : Type u) [Fintype Value] :
    Fintype (CanonicalResponseSignature n Value) :=
  Fintype.ofEquiv
    ((position : Fin n) -> (Fin position.1 -> Value) -> Value)
    (responseTableEquiv n Value).symm

noncomputable instance canonicalResponseSignatureDecidableEq
    (n : Nat) (Value : Type u) :
    DecidableEq (CanonicalResponseSignature n Value) :=
  Classical.decEq _

/-- The response table associated with a named node, obtained by transporting
that node to its unique total-order position. -/
def responseAtNode
    {n : Nat} {Value : Type u}
    (order : FiniteNodeOrder n)
    (signature : CanonicalResponseSignature n Value)
    (node : Fin n) :
    (Fin (order.symm node).1 -> Value) -> Value :=
  signature.response (order.symm node)

/-- Indicator coefficient of a Boolean event on response signatures. -/
def eventCoefficient
    {Signature : Type*}
    (event : Signature -> Bool)
    (signature : Signature) : ℚ :=
  if event signature then 1 else 0

/-- Probability mass assigned to a Boolean event on a finite response-signature
carrier. -/
def signatureEventMass
    {Signature : Type*} [Fintype Signature]
    (mass : Signature -> ℚ)
    (event : Signature -> Bool) : ℚ :=
  ∑ signature, if event signature then mass signature else 0

/-- Every Boolean event query on canonical response signatures is exactly a
finite rational linear objective in the signature masses. -/
theorem signature_event_mass_eq_linearObjective
    {Signature : Type*} [Fintype Signature]
    (mass : Signature -> ℚ)
    (event : Signature -> Bool) :
    signatureEventMass mass event =
      linearObjective (eventCoefficient event) mass := by
  unfold signatureEventMass linearObjective
  apply Finset.sum_congr rfl
  intro signature _
  cases event signature <;> simp [eventCoefficient]

/-- Push an exogenous mass function forward through its deterministic response
signature. -/
def pushforwardSignatureMass
    {Exogenous Signature : Type*}
    [Fintype Exogenous] [DecidableEq Signature]
    (mass : Exogenous -> ℚ)
    (signatureOf : Exogenous -> Signature)
    (signature : Signature) : ℚ :=
  ∑ exogenous,
    if signatureOf exogenous = signature then mass exogenous else 0

/-- Pushing a signature law through the identity exogenous realization returns
the same law. Thus every finite signature-mass witness has an explicit finite
exogenous carrier at the response-signature level. -/
theorem pushforwardSignatureMass_id
    {Signature : Type*}
    [Fintype Signature] [DecidableEq Signature]
    (mass : Signature -> ℚ) :
    pushforwardSignatureMass mass (fun signature => signature) = mass := by
  funext signature
  simp [pushforwardSignatureMass]

/-- Pushforward preserves total mass. -/
theorem pushforwardSignatureMass_total
    {Exogenous Signature : Type*}
    [Fintype Exogenous] [Fintype Signature] [DecidableEq Signature]
    (mass : Exogenous -> ℚ)
    (signatureOf : Exogenous -> Signature) :
    (∑ signature, pushforwardSignatureMass mass signatureOf signature) =
      ∑ exogenous, mass exogenous := by
  unfold pushforwardSignatureMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro exogenous _
  simp

/-- Pushforward preserves nonnegativity of the exogenous mass. -/
theorem pushforwardSignatureMass_nonnegative
    {Exogenous Signature : Type*}
    [Fintype Exogenous] [DecidableEq Signature]
    (mass : Exogenous -> ℚ)
    (mass_nonnegative : forall exogenous, 0 <= mass exogenous)
    (signatureOf : Exogenous -> Signature)
    (signature : Signature) :
    0 <= pushforwardSignatureMass mass signatureOf signature := by
  unfold pushforwardSignatureMass
  apply Finset.sum_nonneg
  intro exogenous _
  split
  · exact mass_nonnegative exogenous
  · exact le_rfl

#print axioms node_has_unique_position
#print axioms signature_event_mass_eq_linearObjective
#print axioms pushforwardSignatureMass_id
#print axioms pushforwardSignatureMass_total

end D5.S3.ConceptDynamics.Causal.PartialIdentification.CanonicalResponseSignature

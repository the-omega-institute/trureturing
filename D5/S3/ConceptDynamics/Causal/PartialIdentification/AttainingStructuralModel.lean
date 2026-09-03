/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/AttainingStructuralModel
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/AttainingStructuralModel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite canonical response-signature probability law is realized by a finite structural model whose shared exogenous state indexes that signature. -/

import D5.S3.ConceptDynamics.Causal.PartialIdentification.CausalOrderLinearProgram

/- Library-search audit trail (2026-09-03):
   * `CanonicalResponseSignature` constructs the finite response carrier and
     proves identity pushforward at the mass-vector level.
   * The 2026 causal-order tightness theorem constructs an SCM attaining every
     optimal signature law by using one exogenous state to index a complete
     deterministic response signature.
   * Repository searches found no causal structure packaging that construction
     together with normalization, nonnegativity, and structural response
     tables. This module supplies that exact finite witness layer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.AttainingStructuralModel

open scoped BigOperators
open D5.S3.ConceptDynamics.Causal.PartialIdentification.CanonicalResponseSignature
open D5.S3.ConceptDynamics.Causal.PartialIdentification.CausalOrderLinearProgram

universe u

/-- A normalized rational probability law on canonical response signatures. -/
structure SignatureProbabilityLaw
    (n : Nat) (Value : Type u) [Fintype Value] where
  mass : CanonicalResponseSignature n Value -> ℚ
  nonnegative : forall signature, 0 <= mass signature
  total : ∑ signature, mass signature = 1

/-- A finite ordered structural model represented by one shared exogenous
variable whose states select complete canonical response signatures. -/
structure OrderedCanonicalSCM
    (n : Nat) (Value : Type u) [Fintype Value] where
  Exogenous : Type u
  exogenousFintype : Fintype Exogenous
  mass : Exogenous -> ℚ
  nonnegative : forall exogenous, 0 <= mass exogenous
  total : @Finset.univ Exogenous exogenousFintype |>.sum mass = 1
  signatureOf : Exogenous -> CanonicalResponseSignature n Value

/-- The deterministic structural equation selected by an exogenous state at a
given total-order position. Its endogenous arguments are exactly the values of
all predecessor positions. -/
def structuralResponse
    {n : Nat} {Value : Type u} [Fintype Value]
    (model : OrderedCanonicalSCM n Value)
    (exogenous : model.Exogenous)
    (position : Fin n) :
    (Fin position.1 -> Value) -> Value :=
  (model.signatureOf exogenous).response position

/-- The response-signature law induced by a finite ordered structural model. -/
noncomputable def inducedSignatureMass
    {n : Nat} {Value : Type u} [Fintype Value]
    (model : OrderedCanonicalSCM n Value) :
    CanonicalResponseSignature n Value -> ℚ := by
  letI : Fintype model.Exogenous := model.exogenousFintype
  exact pushforwardSignatureMass model.mass model.signatureOf

/-- Canonical tightness construction: use the response-signature carrier itself
as the exogenous state space, retain the proposed signature law, and let each
exogenous state select itself. -/
noncomputable def canonicalSCMOfSignatureLaw
    {n : Nat} {Value : Type u} [Fintype Value]
    (law : SignatureProbabilityLaw n Value) :
    OrderedCanonicalSCM n Value where
  Exogenous := CanonicalResponseSignature n Value
  exogenousFintype := inferInstance
  mass := law.mass
  nonnegative := law.nonnegative
  total := law.total
  signatureOf := fun signature => signature

/-- The canonical structural model induces exactly the nominated signature
probability law. -/
theorem canonicalSCM_inducedSignatureMass
    {n : Nat} {Value : Type u} [Fintype Value]
    (law : SignatureProbabilityLaw n Value) :
    inducedSignatureMass (canonicalSCMOfSignatureLaw law) = law.mass := by
  unfold inducedSignatureMass canonicalSCMOfSignatureLaw
  exact pushforwardSignatureMass_id law.mass

/-- Each structural equation in the canonical witness is exactly the response
table stored by its exogenous signature state. -/
theorem canonicalSCM_structuralResponse
    {n : Nat} {Value : Type u} [Fintype Value]
    (law : SignatureProbabilityLaw n Value)
    (signature : CanonicalResponseSignature n Value)
    (position : Fin n) :
    structuralResponse
        (canonicalSCMOfSignatureLaw law) signature position =
      signature.response position := by
  rfl

/-- Every Boolean counterfactual event has the same probability in the
canonical attaining SCM as in the original signature-law LP witness. -/
theorem canonicalSCM_attains_signature_event
    {n : Nat} {Value : Type u} [Fintype Value]
    (law : SignatureProbabilityLaw n Value)
    (event : CanonicalResponseSignature n Value -> Bool) :
    exogenousEventMass
        (canonicalSCMOfSignatureLaw law).mass
        (canonicalSCMOfSignatureLaw law).signatureOf
        event =
      signatureEventMass law.mass event := by
  rfl

/-- The induced response-signature law of every normalized finite ordered SCM
is normalized. -/
theorem inducedSignatureMass_total
    {n : Nat} {Value : Type u} [Fintype Value]
    (model : OrderedCanonicalSCM n Value) :
    ∑ signature, inducedSignatureMass model signature = 1 := by
  letI : Fintype model.Exogenous := model.exogenousFintype
  rw [inducedSignatureMass, pushforwardSignatureMass_total]
  exact model.total

/-- The induced response-signature law of every finite ordered SCM is
nonnegative. -/
theorem inducedSignatureMass_nonnegative
    {n : Nat} {Value : Type u} [Fintype Value]
    (model : OrderedCanonicalSCM n Value)
    (signature : CanonicalResponseSignature n Value) :
    0 <= inducedSignatureMass model signature := by
  letI : Fintype model.Exogenous := model.exogenousFintype
  exact pushforwardSignatureMass_nonnegative
    model.mass model.nonnegative model.signatureOf signature

#print axioms canonicalSCM_inducedSignatureMass
#print axioms canonicalSCM_structuralResponse
#print axioms canonicalSCM_attains_signature_event
#print axioms inducedSignatureMass_total
#print axioms inducedSignatureMass_nonnegative

end D5.S3.ConceptDynamics.Causal.PartialIdentification.AttainingStructuralModel

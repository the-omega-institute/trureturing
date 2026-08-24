/- GID: D5/S3/ConceptDynamics/DefinitionEscape/InvolutiveBlindResidual
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hidden involutions generate blind residuals and primitive semantic escape. -/

import D5.S3.ConceptDynamics.DefinitionEscape.OrbitOrientation
import D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.InvolutiveBlindResidual

universe u v w z t

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
open D5.S3.ConceptDynamics.DefinitionEscape.InvolutiveNegation
open D5.S3.ConceptDynamics.DefinitionEscape.OrbitOrientation

/-- Every member of a definition family hides the supplied involution. -/
def FamilyHidden
    {X : Type u} {InputOutput : Type v}
    (negation : InvolutiveNegation X)
    (Gamma : Set (Concept X InputOutput)) : Prop :=
  ∀ definition : Gamma,
    HiddenReadout negation definition.1

/-- A family-hidden involution pair belongs to the common kernel of the whole
definition language. -/
theorem familyHidden_pair_mem_jointKernel
    {X : Type u} {InputOutput : Type v}
    (negation : InvolutiveNegation X)
    (Gamma : Set (Concept X InputOutput))
    (familyHidden : FamilyHidden negation Gamma) (x : X) :
    (x, negation.neg x) ∈
      jointKernel (fun definition : Gamma => definition.1) := by
  simp only [jointKernel, conceptKernel, Set.mem_iInter, Set.mem_setOf_eq]
  intro definition
  exact (familyHidden definition x).symm

/-- Semantic closure preserves every symmetry hidden by the generating
definition family. -/
theorem semanticClosure_hidden_of_familyHidden
    {X : Type u} {InputOutput : Type v} {Output : Type w}
    (negation : InvolutiveNegation X)
    (Gamma : Set (Concept X InputOutput))
    (familyHidden : FamilyHidden negation Gamma)
    (candidate : Concept X Output)
    (inside : candidate ∈ SemanticClosure Gamma) :
    HiddenReadout negation candidate := by
  intro x
  apply inside
  have pairInKernel :=
    familyHidden_pair_mem_jointKernel
      negation Gamma familyHidden (negation.neg x)
  simpa only [negation.involutive x] using pairInKernel

/-- If the current readout and every old definition hide an involution while a
target distinguishes one orbit, that orbit is a target-relevant blind
residual. -/
theorem hidden_involution_pair_mem_blindResidual
    {X : Type u} {Current : Type v} {InputOutput : Type w}
    {Target : Type z}
    (negation : InvolutiveNegation X)
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current) (target : Concept X Target)
    (currentHidden : HiddenReadout negation current)
    (familyHidden : FamilyHidden negation Gamma)
    (x : X) (targetDifferent : target x ≠ target (negation.neg x)) :
    (x, negation.neg x) ∈ blindResidual Gamma current target := by
  refine ⟨⟨(currentHidden x).symm, targetDifferent⟩, ?_⟩
  exact familyHidden_pair_mem_jointKernel
    negation Gamma familyHidden x

/-- A Boolean target negated by a symmetry hidden from the old language has a
nonempty blind residual on every inhabited source. -/
theorem negating_target_blindResidual_nonempty
    {X : Type u} {Current : Type v} {InputOutput : Type w}
    [Nonempty X]
    (negation : InvolutiveNegation X)
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current) (target : Concept X Bool)
    (currentHidden : HiddenReadout negation current)
    (familyHidden : FamilyHidden negation Gamma)
    (targetNegating : NegatingReadout negation target) :
    (blindResidual Gamma current target).Nonempty := by
  rcases ‹Nonempty X› with ⟨x⟩
  refine ⟨(x, negation.neg x), ?_⟩
  exact hidden_involution_pair_mem_blindResidual
    negation Gamma current target currentHidden familyHidden x
    (negatingReadout_pair_ne negation target targetNegating x)

/-- A Boolean candidate negated by the same hidden symmetry productively
separates the target blind residual. -/
theorem negating_candidate_productiveSeparation
    {X : Type u} {Current : Type v} {InputOutput : Type w}
    (negation : InvolutiveNegation X)
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current)
    (target candidate : Concept X Bool)
    (currentHidden : HiddenReadout negation current)
    (familyHidden : FamilyHidden negation Gamma)
    (targetNegating : NegatingReadout negation target)
    (candidateNegating : NegatingReadout negation candidate)
    (x : X) :
    ProductiveSeparation Gamma current target candidate := by
  refine ⟨x, negation.neg x, ?_, ?_⟩
  · exact hidden_involution_pair_mem_blindResidual
      negation Gamma current target currentHidden familyHidden x
      (negatingReadout_pair_ne negation target targetNegating x)
  · exact negatingReadout_pair_ne
      negation candidate candidateNegating x

/-- Productive separation along a hidden involution necessarily escapes the
complete semantic closure of the old definition family. -/
theorem negating_candidate_primitiveEscape
    {X : Type u} {Current : Type v} {Input�Utput : Type w}
    [Nonempty X]
    (negation : InvolutiveNegation X)
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current)
    (target candidate : Concept X Bool)
    (currentHidden : HiddenReadout negation current)
    (familyHidden : FamilyHidden negation Gamma)
    (targetNegating : NegatingReadout negation target)
    (candidateNegating : NegatingReadout negation candidate) :
    PrimitiveEscape Gamma candidate := by
  rcases ‹Nonempty X› with ⟨x⟩
  apply productiveSeparation_implies_primitiveEscape
    Gamma current target candidate
  exact negating_candidate_productiveSeparation
    negation Gamma current target candidate currentHidden familyHidden
      targetNegating candidateNegating x

/-- Even without a target, every Boolean readout negated by a family-hidden
involution lies outside the family's semantic closure. -/
theorem negatingReadout_not_mem_semanticClosure
    {X : Type u} {InputOutput : Type v}
    [Nonempty X]
    (negation : InvolutiveNegation X)
    (Gamma : Set (Concept X InputOutput))
    (familyHidden : FamilyHidden negation Gamma)
    (candidate : Concept X Bool)
    (candidateNegating : NegatingReadout negation candidate) :
    candidate ∉ SemanticClosure Gamma := by
  intro inside
  have candidateHidden :=
    semanticClosure_hidden_of_familyHidden
      negation Gamma familyHidden candidate inside
  rcases ‹Nonempty X› with ⟨x⟩
  exact
    (negatingReadout_pair_ne negation candidate candidateNegating x)
      (hiddenReadout_pair_equal negation candidate candidateHidden x)

/-- The complete structured-negation chain packages blind residual,
productive separation, and primitive escape. -/
theorem structured_negation_escape_chain
    {X : Type u} {Current : Type v} {InputOutput : Type w}
    [Nonempty X]
    (negation : InvolutiveNegation X)
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current)
    (target candidate : Concept X Bool)
    (currentHidden : HiddenReadout negation current)
    (familyHidden : FamilyHidden negation Gamma)
    (targetNegating : NegatingReadout negation target)
    (candidateNegating : NegatingReadout negation candidate) :
    (blindResidual Gamma current target).Nonempty ∧
      ProductiveSeparation Gamma current target candidate ∧
      PrimitiveEscape Gamma candidate := by
  rcases ‹Nonempty X› with ⟨x⟩
  have blindPair :=
    hidden_involution_pair_mem_blindResidual
      negation Gamma current target currentHidden familyHidden x
      (negatingReadout_pair_ne negation target targetNegating x)
  have productive :
      ProductiveSeparation Gamma current target candidate :=
    ⟨x, negation.neg x, blindPair,
      negatingReadout_pair_ne negation candidate candidateNegating x⟩
  exact
    ⟨⟨(x, negation.neg x), blindPair⟩, productive,
      productiveSeparation_implies_primitiveEscape
        Gamma current target candidate productive⟩

#print axioms semanticClosure_hidden_of_familyHidden
#print axioms negating_target_blindResidual_nonempty
#print axioms negating_candidate_primitiveEscape
#print axioms negatingReadout_not_mem_semanticClosure
#print axioms structured_negation_escape_chain

end D5.S3.ConceptDynamics.DefinitionEscape.InvolutiveBlindResidual

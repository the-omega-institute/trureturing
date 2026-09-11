/- GID: D5/S3/ConceptDynamics/ZfcPropositional/IntEntailmentTwo
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcPropositional/IntEntailmentTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Propositional.Entailment.Int for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcEntailment.EntailmentTwo
public import D5.S3.ConceptDynamics.ZfcFiniteCollections.Finset
public import D5.S3.ConceptDynamics.ZfcMinimalLogic.MinimalEntailmentFour
public import D5.S3.ConceptDynamics.ZfcPropositional.IntEntailmentOne

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Propositional/Entailment/Int.lean, original lines 310-463.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section
namespace LO
namespace Entailment
variable {F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F]
         {S : Type*} [Entailment S F]
         {𝓢 : S}
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}
variable [Entailment.Int 𝓢]
open NegationEquiv
open FiniteContext
open List
section disjunction

end disjunction

section

variable {Γ Δ : Finset F}

end

section

end

section consistency

omit [DecidableEq F] in
lemma inconsistent_of_provable_of_unprovable {φ : F}
    (hp : 𝓢 ⊢ φ) (hn : 𝓢 ⊢ ∼φ) : Inconsistent 𝓢 := by
  have : 𝓢 ⊢ φ 🡒 ⊥ := N!_iff_CO!.mp hn
  intro ψ; exact efq! ⨀ (this ⨀ hp)

end consistency

end LO.Entailment

end

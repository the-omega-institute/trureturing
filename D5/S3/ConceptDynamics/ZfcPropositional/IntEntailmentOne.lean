/- GID: D5/S3/ConceptDynamics/ZfcPropositional/IntEntailmentOne
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcPropositional/IntEntailmentOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Propositional.Entailment.Int for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcEntailment.EntailmentTwo
public import D5.S3.ConceptDynamics.ZfcFiniteCollections.Finset
public import D5.S3.ConceptDynamics.ZfcMinimalLogic.MinimalEntailmentFour

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Propositional/Entailment/Int.lean, original lines 1-309.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F]
variable (φ ψ χ : F)

protected abbrev EFQ := ⊥ 🡒 φ

end LO.Axioms

namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [LogicalNeutral F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomEFQ (𝓢 : S)  where
  efq {φ : F} : 𝓢 ⊢! Axioms.EFQ φ
export HasAxiomEFQ (efq)

@[simp] lemma efq! [Entailment.HasAxiomEFQ 𝓢] : 𝓢 ⊢ ⊥ 🡒 φ := ⟨efq⟩

section

variable [Entailment.Minimal 𝓢]

namespace FiniteContext

end FiniteContext

namespace Context

end Context

end

end LO.Entailment

namespace LO.Entailment

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F]
         {S : Type*} [Entailment S F]
         {𝓢 : S}
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}

protected class Int (𝓢 : S) extends Entailment.Minimal 𝓢, Entailment.HasAxiomEFQ 𝓢

variable [Entailment.Int 𝓢]

namespace FiniteContext

end FiniteContext

namespace Context

end Context

open NegationEquiv
open FiniteContext
open List

section Conjunction

end Conjunction

section disjunction

end disjunction
end Entailment
end LO
end

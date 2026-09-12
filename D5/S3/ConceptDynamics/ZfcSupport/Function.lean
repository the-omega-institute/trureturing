/- GID: D5/S3/ConceptDynamics/ZfcSupport/Function
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcSupport/Function
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Basic]
   utility: none
   digest: Vorspiel.Function for first-order set definition elimination. -/
module

public import Mathlib.Data.Fintype.Basic

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/Function.lean, original lines 1-18.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace Function

variable  {α : Type u} {β : Type v}

def funEqOn (φ : α → Prop) (f g : α → β) : Prop := ∀ a, φ a → f a = g a

lemma funEqOn.of_subset {φ ψ : α → Prop} {f g : α → β} (e : funEqOn φ f g) (h : ∀ a, ψ a → φ a) : funEqOn ψ f g :=
  by intro a ha; exact e a (h a ha)

end Function

end

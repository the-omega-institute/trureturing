/- GID: D5/S3/ConceptDynamics/ZfcPredicate/LanguageOne
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcPredicate/LanguageOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Encodable.Basic]
   utility: none
   digest: Syntax.Predicate.Language for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcEntailment.EntailmentTwo
public import Mathlib.Logic.Encodable.Basic

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Syntax/Predicate/Language.lean, original lines 1-318.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO

namespace FirstOrder

structure Language where
  Func : Nat → Type u
  Rel  : Nat → Type u

namespace Language

namespace ORing

end ORing

namespace ORing

end ORing

namespace Constant

variable (C : Type*)

end Constant

section Constant

variable (C : Type*)

--instance : Coe (Type*) Language := ⟨constant⟩

end Constant

protected class Eq (L : Language) where
  eq : L.Rel 2

protected class Mem (L : Language) where
  mem : L.Rel 2

attribute [match_pattern] Eq.eq Mem.mem

end Language
end FirstOrder
end LO
end

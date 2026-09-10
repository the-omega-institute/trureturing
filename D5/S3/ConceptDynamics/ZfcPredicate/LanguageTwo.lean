/- GID: D5/S3/ConceptDynamics/ZfcPredicate/LanguageTwo
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcPredicate/LanguageTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Encodable.Basic]
   utility: none
   digest: Syntax.Predicate.Language for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcEntailment.EntailmentTwo
public import Mathlib.Logic.Encodable.Basic
public import D5.S3.ConceptDynamics.ZfcPredicate.LanguageOne

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Syntax/Predicate/Language.lean, original lines 319-445.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section
namespace LO
namespace FirstOrder
namespace Language

@[ext] structure Hom (L₁ L₂ : Language) where
  func : {k : ℕ} → L₁.Func k → L₂.Func k
  rel : {k : ℕ} → L₁.Rel k → L₂.Rel k

/--
A structure for the homomorphisms (respecting function and relation symbols) between first-order languages.
-/
scoped[LO.FirstOrder] infix:25 " →ᵥ " => LO.FirstOrder.Language.Hom

namespace Hom
variable (L L₁ L₂ L₃ : Language) (Φ : Hom L₁ L₂)

variable {L L₁ L₂ L₃}

end Hom

end Language

protected class Language.DecidableEq (L : Language) where
  func : (k : ℕ) → DecidableEq (L.Func k)
  rel : (k : ℕ) → DecidableEq (L.Rel k)

instance (L : Language) [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] : L.DecidableEq :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance (L : Language) [L.DecidableEq] (k : ℕ) : DecidableEq (L.Func k) := Language.DecidableEq.func k

instance (L : Language) [L.DecidableEq] (k : ℕ) : DecidableEq (L.Rel k) := Language.DecidableEq.rel k

protected class Language.Encodable (L : Language) where
  func : (k : ℕ) → Encodable (L.Func k)
  rel : (k : ℕ) → Encodable (L.Rel k)

instance (L : Language) [L.Encodable] (k : ℕ) : Encodable (L.Func k) := Language.Encodable.func k

instance (L : Language) [L.Encodable] (k : ℕ) : Encodable (L.Rel k) := Language.Encodable.rel k

end FirstOrder

end LO
end

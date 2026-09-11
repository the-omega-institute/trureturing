/- GID: D5/S3/ConceptDynamics/ZfcTermRewriting/RewFour
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcTermRewriting/RewFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Syntax.Predicate.Rew for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcPredicate.Quantifier
public import D5.S3.ConceptDynamics.ZfcPredicate.Term
public import D5.S3.ConceptDynamics.ZfcSupport.Function
public import D5.S3.ConceptDynamics.ZfcTermRewriting.RewThree

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Syntax/Predicate/Rew.lean, original lines 954-1080.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section
namespace LO
namespace FirstOrder
namespace LawfulSyntacticRewriting
variable {S : ℕ → Type*} [LCWQ S] [SyntacticRewriting L S S]
open Rewriting ReflectiveRewriting TransitiveRewriting InjMapRewriting Semiterm
variable [LawfulSyntacticRewriting L S]

lemma free_rewrite_eq (f : ℕ → SyntacticTerm L) (φ : S 1) :
    free ((Rew.rewrite fun x ↦ Rew.bShift (f x)) ▹ φ) =
    Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x)) ▹ free φ := by
  simpa [← comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

lemma shift_rewrite_eq (f : ℕ → SyntacticTerm L) (φ : S 0) :
    shift (Rew.rewrite f ▹ φ) = (Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x))) ▹ shift φ := by
  simpa [←comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

lemma rewrite_subst_eq (f : ℕ → SyntacticTerm L) (t) (φ : S 1) :
    Rew.rewrite f ▹ φ/[t] = (Rew.rewrite (Rew.bShift ∘ f) ▹ φ)/[Rew.rewrite f t] := by
  simpa [←comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

@[simp] lemma free_subst_nil (φ : S 0) : free (Rewriting.subst (ξ := ℕ) φ ![]) = shift φ := by
  simpa [←comp_app] using smul_ext' <| by
    ext x <;> simp only [Rew.comp_app, Rew.subst_fvar, Rew.free_fvar, Rew.shift_fvar]; { exact Fin.elim0 x }

lemma rewrite_subst_nil (f : ℕ → SyntacticTerm L) (φ : S 0) :
    Rew.rewrite (Rew.bShift ∘ f) ▹ (Rewriting.subst (ξ := ℕ) φ ![]) =
    Rewriting.subst (ξ := ℕ) (Rew.rewrite f ▹ φ) ![] := by
  simpa [←comp_app] using smul_ext' <| by
    ext x
    · exact x.elim0
    · simp [Rew.comp_app, Rew.bShift_eq_rewrite]

@[simp] lemma cast_subst_eq (t : SyntacticTerm L) (φ : S 0) :
    (Rewriting.subst (ξ := ℕ) φ ![])/[t] = φ := by
  suffices (Rewriting.subst (ξ := ℕ) φ ![])/[t] = Rew.id ▹ φ by rwa [ReflectiveRewriting.id_app] at this
  simpa [←comp_app, -id_app] using smul_ext' <| by
    ext x <;> simp only [Rew.comp_app, Rew.subst_bvar, Rew.subst_fvar, Rew.id_app]
    exact x.elim0

lemma rewrite_free_eq_subst (t : SyntacticTerm L) (φ : S 1) :
    Rew.rewrite (t :>ₙ fun x ↦ &x) ▹ free φ = φ/[t] := by
  simpa [←comp_app] using smul_ext' <| by ext x <;> simp [Rew.comp_app]

end LawfulSyntacticRewriting

namespace Rewriting

variable {ο ξ : Type*} [IsEmpty ο] {O F F₁ F₂ : ℕ → Type*} [LCWQ O] [LCWQ F] [LCWQ F₁] [LCWQ F₂]

open ReflectiveRewriting TransitiveRewriting InjMapRewriting Semiterm

variable {S : ℕ → Type*} [LCWQ S] [SyntacticRewriting L S S] [LawfulSyntacticRewriting L S]

end Rewriting

end FirstOrder

end LO

end

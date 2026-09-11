/- GID: D5/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcTermRewriting/RewThreeCompat
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Canonical ASCII selectors for the punctuation-bearing RewThree declarations. -/
module

public import D5.S3.ConceptDynamics.ZfcTermRewriting.RewThree

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Syntax/Predicate/Rew.lean, original lines 638-953.
   Modifications: an isolated compatibility wrapper only; the frozen RewThree source
   remains unchanged. The wrappers provide canonical ASCII GID selectors for source
   names containing `?` or `₂`. Apache-2.0 license: Library/ConceptDynamics/
   foundation2026firstorder.md. -/

@[expose] public section
namespace LO
namespace FirstOrder

namespace Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

lemma fvar_rew [DecidableEq ξ₁] [DecidableEq ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {t : Semiterm L ξ₁ n₁} {x} :
    (ω t).FVar? x → (∃ i : Fin n₁, (ω #i).FVar? x) ∨
      (∃ z : ξ₁, t.FVar? z ∧ (ω &z).FVar? x) :=
  fvar?_rew

@[simp] lemma fvar_bShift [DecidableEq ξ] {t : Semiterm L ξ n} {x} :
    (Rew.bShift t).FVar? x ↔ t.FVar? x :=
  fvar?_bShift

end Semiterm

namespace RewThreeCompat

variable {L : Language} {S : ℕ → Type*} [LCWQ S]
  [SyntacticRewriting L S S]

open Rewriting

lemma shift_conj_two (Γ : List (S n)) : shift (⋀Γ) = ⋀Γ⁺ :=
  LawfulSyntacticRewriting.shift_conj₂ Γ

variable [LawfulSyntacticRewriting L S]

lemma app_subst_fbar_zero_comp_shift_eq_free (φ : S 1) :
    (shift φ)/[&0] = free φ :=
  LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free φ

variable {F : ℕ → Type*}

lemma shifts_nil [LCWQ F] [Rewriting L ℕ F ℕ F] :
    ([] : List (F n))⁺ = [] :=
  Rewriting.shifts_nil

lemma shifts_cons [LCWQ F] [Rewriting L ℕ F ℕ F] (φ : F n) (Γ : List (F n)) :
    (φ :: Γ)⁺ = Rewriting.shift φ :: Γ⁺ :=
  Rewriting.shifts_cons φ Γ

lemma shifts_neg [LCWQ F] [Rewriting L ℕ F ℕ F] (Γ : List (F n)) :
    (∼Γ)⁺ = ∼(Γ⁺) :=
  Rewriting.shifts_neg Γ

abbrev emb {ο ξ} [IsEmpty ο] {O F : ℕ → Type*} [LCWQ O] [LCWQ F]
    [Rewriting L ο O ξ F] : O n →ˡᶜ F n :=
  Rewriting.emb (L := L) (n := n) (ο := ο) (ξ := ξ) (O := O) (F := F)

/-- Addressable typed substitution; slash-vector syntax is supplied by RewThree. -/
abbrev substNotation {ξ : Type*} [LCWQ F] [Rewriting L ξ F ξ F]
    (φ : F n₁) (w : Fin n₁ → Semiterm L ξ n₂) : F n₂ :=
  Rewriting.subst φ w

end RewThreeCompat

end FirstOrder
end LO
end

/- GID: D5/S3/ConceptDynamics/ZfcEntailment/EntailmentTwo
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcEntailment/EntailmentTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logic.Entailment for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcLogic.Semantics
public import D5.S3.ConceptDynamics.ZfcSupport.AdjunctiveSet
public import D5.S3.ConceptDynamics.ZfcEntailment.EntailmentOne

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Logic/Entailment.lean, original lines 321-645.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section
namespace LO
namespace Entailment
variable {F : Type*} {S T U : Type*} [Entailment S F] [Entailment T F] [Entailment U F]
variable (S)
variable {S}
section
variable [Tilde F] (𝓢 : S)
variable {𝓢}

end

variable (S T)

class Axiomatized [AdjunctiveSet F S] where
  prfAxm {𝓢 : S} : 𝓢 ⊢!* AdjunctiveSet.set 𝓢
  weakening {𝓢 𝓣 : S} : 𝓢 ⊆ 𝓣 → 𝓢 ⊢! φ → 𝓣 ⊢! φ

variable {S T}

section Axiomatized

namespace Axiomatized

variable [AdjunctiveSet F S] [Axiomatized S] {𝓢 𝓣 : S}

def byAxm {𝓢 : S} (h : φ ∈ 𝓢) : 𝓢 ⊢! φ := prfAxm (by simp [h])

lemma by_axm {𝓢 : S} (h : φ ∈ 𝓢) : 𝓢 ⊢ φ := ⟨byAxm h⟩

@[simp] lemma provable_refl (𝓢 : S) : 𝓢 ⊢* AdjunctiveSet.set 𝓢 := fun hf ↦ ⟨prfAxm hf⟩

@[simp] theorem adjoin! (φ : F) (𝓢 : S) : adjoin φ 𝓢 ⊢ φ := provable_refl _ (by simp)

lemma weakening! (h : 𝓢 ⊆ 𝓣 := by simp) {φ} : 𝓢 ⊢ φ → 𝓣 ⊢ φ := by rintro ⟨b⟩; exact ⟨weakening h b⟩

abbrev weakerThanOfSubset (h : 𝓢 ⊆ 𝓣) : 𝓢 ⪯ 𝓣 := ⟨fun _ ↦ weakening! h⟩

theorem to_adjoin {𝓢 : S} : 𝓢 ⊢ ψ → adjoin φ 𝓢 ⊢ ψ := fun b ↦ weakening! (by simp) b

end Axiomatized

alias by_axm := Axiomatized.by_axm
alias wk! := Axiomatized.weakening!

section axiomatized

variable [AdjunctiveSet F S] [AdjunctiveSet F T] [Axiomatized S]

end axiomatized

namespace StrongCut

end StrongCut

abbrev WeakerThan.ofSubset [AdjunctiveSet F S] [Axiomatized S] {𝓢 𝓣 : S} (h : 𝓢 ⊆ 𝓣) : 𝓢 ⪯ 𝓣 := ⟨fun _ ↦ wk! h⟩

variable (S)

variable {S}

namespace Compact

end Compact

end Axiomatized

end Entailment

namespace Entailment

variable {S : Type*} {F : Type*} [LogicalConnective F] [LogicalNeutral F] [Entailment S F]

section

end

variable (S)

class Deduction [Adjoin F S] where
  ofInsert {φ ψ : F} {𝓢 : S} : adjoin φ 𝓢 ⊢! ψ → 𝓢 ⊢! φ 🡒 ψ
  inv {φ ψ : F} {𝓢 : S} : 𝓢 ⊢! φ 🡒 ψ → adjoin φ 𝓢 ⊢! ψ

variable {S}

section deduction

variable [Adjoin F S] [Deduction S] {𝓢 : S} {φ ψ : F}

omit [LogicalNeutral F] in
lemma Deduction.of_insert! (h : adjoin φ 𝓢 ⊢ ψ) : 𝓢 ⊢ φ 🡒 ψ := by
  rcases h with ⟨b⟩; exact ⟨Deduction.ofInsert b⟩

end deduction

end Entailment

section

variable {S : Type*} {F : Type*} [Entailment S F] {M : Type*} [Semantics M F]

class Sound (𝓢 : S) (𝓜 : M) : Prop where
  sound : ∀ {φ : F}, 𝓢 ⊢ φ → 𝓜 ⊧ φ

namespace Sound

section

variable {𝓢 𝓣 : S} {𝓜 𝓝 : M} [Sound 𝓢 𝓜] [Sound 𝓣 𝓝]

lemma consistent_of_meaningful : Semantics.Meaningful 𝓜 → Entailment.Consistent 𝓢 :=
  fun H ↦ ⟨fun h ↦ by rcases H with ⟨φ, hf⟩; exact hf (Sound.sound (h φ))⟩

end

section

variable {𝓢 : S} {T : Set F} [Sound 𝓢 (Semantics.models M T)]

lemma consistent_of_satisfiable [∀ 𝓜 : M, Semantics.Meaningful 𝓜] : Semantics.Satisfiable M T → Entailment.Consistent 𝓢 :=
  fun H ↦ consistent_of_meaningful (Semantics.meaningful_iff_satisfiableSet.mp H)

end

end Sound

namespace Complete

section

end

section

section

end

end

end Complete

end

namespace Entailment

variable (S : Type*) {F : Type*} [Entailment S F]

structure Pullback (f : G → F) : Type _ where
  forget : S

variable {S}

abbrev pullback (𝓢 : S) (f : G → F) : Pullback S f := ⟨𝓢⟩

instance (f : G → F) : Entailment (Pullback S f) G where
  Prf := fun 𝓢 φ ↦ 𝓢.forget ⊢! f φ

namespace Pullback

section basics

variable {f : G → F}

end basics

end Pullback

end Entailment

end LO

end

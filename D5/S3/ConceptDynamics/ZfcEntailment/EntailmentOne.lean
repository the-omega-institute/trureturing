/- GID: D5/S3/ConceptDynamics/ZfcEntailment/EntailmentOne
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcEntailment/EntailmentOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logic.Entailment for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcLogic.Semantics
public import D5.S3.ConceptDynamics.ZfcSupport.AdjunctiveSet

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Logic/Entailment.lean, original lines 1-320.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO

/-- Entailment relation on proof system `S` and formula `F` -/
class Entailment (S : Type*) (F : outParam Type*) where
  Prf : S → F → Type*

infix:45 " ⊢! " => Entailment.Prf

namespace Entailment

variable {F : Type*} {S T U : Type*} [Entailment S F] [Entailment T F] [Entailment U F]

section

variable (𝓢 : S)

/-- Proposition that states `φ` is provable. -/
def Provable (φ : F) : Prop := Nonempty (𝓢 ⊢! φ)

/-- Abbreviation for unprovability. -/
abbrev Unprovable (φ : F) : Prop := ¬Provable 𝓢 φ

infix:45 " ⊢ " => Provable

infix:45 " ⊬ " => Unprovable

/-- Proofs of set of formulae. -/
def PrfSet (s : Set F) : Type _ := ⦃φ : F⦄ → φ ∈ s → 𝓢 ⊢! φ

/-- Proposition for existance of proofs of set of formulae. -/
def ProvableSet (s : Set F) : Prop := ∀ {φ}, φ ∈ s → 𝓢 ⊢ φ

infix:45 " ⊢!* " => PrfSet

infix:45 " ⊢* " => ProvableSet

/-- Set of all provable formulae. -/
def theory : Set F := {φ | 𝓢 ⊢ φ}

end

def cast {𝓢 : S} {φ ψ : F} (b : 𝓢 ⊢! φ) (e : φ = ψ := by simp) : 𝓢 ⊢! ψ := e ▸ b

noncomputable def Provable.get {𝓢 : S} {φ : F} (h : 𝓢 ⊢ φ) : 𝓢 ⊢! φ :=
  Classical.choice h

/-- Provability strength relation of proof systems -/
class WeakerThan (𝓢 : S) (𝓣 : T) : Prop where
  subset : theory 𝓢 ⊆ theory 𝓣

infix:40 " ⪯ " => WeakerThan

section WeakerThan

variable {𝓢 : S} {𝓣 : T} {𝓤 : U}

lemma WeakerThan.pbl [h : 𝓢 ⪯ 𝓣] {φ} : 𝓢 ⊢ φ → 𝓣 ⊢ φ := @h.subset φ

@[trans] lemma WeakerThan.trans : 𝓢 ⪯ 𝓣 → 𝓣 ⪯ 𝓤 → 𝓢 ⪯ 𝓤 := fun w₁ w₂ ↦ ⟨Set.Subset.trans w₁.subset w₂.subset⟩

end WeakerThan

def Inconsistent (𝓢 : S) : Prop := ∀ φ, 𝓢 ⊢ φ

class Consistent (𝓢 : S) : Prop where
  not_inconsistent : ¬Inconsistent 𝓢

@[simp] lemma not_inconsistent_iff_consistent {𝓢 : S} :
    ¬Inconsistent 𝓢 ↔ Consistent 𝓢 :=
  ⟨fun h ↦ ⟨h⟩, by rintro ⟨h⟩; exact h⟩

variable (S)

class DeductiveExplosion [LogicalNeutral F] where
  dexp {𝓢 : S} : 𝓢 ⊢! ⊥ → (φ : F) → 𝓢 ⊢! φ

variable {S}

section

variable [LogicalNeutral F] [DeductiveExplosion S]

theorem DeductiveExplosion.dexp! {𝓢 : S} (h : 𝓢 ⊢ ⊥) (φ : F) : 𝓢 ⊢ φ := by
  rcases h with ⟨b⟩; exact ⟨dexp b φ⟩

lemma inconsistent_iff_provable_bot {𝓢 : S} :
    Inconsistent 𝓢 ↔ 𝓢 ⊢ ⊥ := ⟨fun h ↦ h ⊥, fun h φ ↦ DeductiveExplosion.dexp! h φ⟩

lemma consistent_iff_unprovable_bot {𝓢 : S} :
    Consistent 𝓢 ↔ 𝓢 ⊬ ⊥ := by
  simp [inconsistent_iff_provable_bot, ←not_inconsistent_iff_consistent]

end

section

variable [Tilde F] (𝓢 : S)

variable {𝓢}

end
end Entailment
end LO
end

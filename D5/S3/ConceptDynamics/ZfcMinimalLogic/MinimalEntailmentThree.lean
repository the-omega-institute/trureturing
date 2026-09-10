/- GID: D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentThree
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Propositional.Entailment.Minimal for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcEntailment.EntailmentTwo
public import D5.S3.ConceptDynamics.ZfcFiniteCollections.Finset
public import D5.S3.ConceptDynamics.ZfcMinimalLogic.MinimalEntailmentTwo

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Propositional/Entailment/Minimal.lean, original lines 640-959.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section
namespace LO
namespace Entailment
section
variable (F)
variable {F}
namespace Context
variable {𝓢 : S}
variable [LogicalConnective F] [LogicalNeutral F] [Entailment S F]
variable (𝓢)

notation Γ:45 " *⊢[" 𝓢 "]! " φ:46 => Prf 𝓢 Γ φ

notation Γ:45 " *⊢[" 𝓢 "] " φ:46 => Provable 𝓢 Γ φ

section

variable {𝓢}

section minimal

variable [Entailment.Minimal 𝓢]

-- lemma provable_iff' [DecidableEq F] {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ : Finset F, (↑Δ ⊆ Γ) ∧ Δ *⊢[𝓢] φ

def deduct [DecidableEq F] {φ ψ : F} {Γ : Set F} : (insert φ Γ) *⊢[𝓢]! ψ → Γ *⊢[𝓢]! φ 🡒 ψ
  | ⟨Δ, h, b⟩ =>
    have h : ∀ ψ ∈ Δ, ψ = φ ∨ ψ ∈ Γ := by simpa using h
    let b' : (φ :: Δ.filter (· ≠ φ)) ⊢[𝓢]! ψ :=
      FiniteContext.weakening
        (by simp [List.subset_def, List.mem_filter]; grind)
        b
    ⟨ Δ.filter (· ≠ φ), by
      intro ψ
      suffices ψ ∈ Δ → ψ ≠ φ → ψ ∈ Γ by simpa [List.mem_filter]
      intro hq ne
      rcases h ψ hq
      · contradiction
      · assumption,
      FiniteContext.deduct b' ⟩
lemma deduct! [DecidableEq F] (h : (insert φ Γ) *⊢[𝓢] ψ) : Γ *⊢[𝓢] φ 🡒 ψ := ⟨Context.deduct h.some⟩

def deductInv {φ ψ : F} {Γ : Set F} : Γ *⊢[𝓢]! φ 🡒 ψ → (insert φ Γ) *⊢[𝓢]! ψ
  | ⟨Δ, h, b⟩ => ⟨φ :: Δ, by simpa using fun χ hr ↦ Or.inr (h χ hr), FiniteContext.deductInv b⟩
lemma deductInv! [DecidableEq F] (h : Γ *⊢[𝓢] φ 🡒 ψ) : (insert φ Γ) *⊢[𝓢] ψ := ⟨Context.deductInv h.some⟩

def of {φ : F} (b : 𝓢 ⊢! φ) : Γ *⊢[𝓢]! φ := ⟨[], by simp, FiniteContext.of b⟩

lemma of! (b : 𝓢 ⊢ φ) : Γ *⊢[𝓢] φ := ⟨Context.of b.some⟩

end minimal

end

end Context

end

section

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F]
         {S : Type*} [Entailment S F]
         {𝓢 : S} [Entailment.Minimal 𝓢]
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}

open NegationEquiv
open FiniteContext
open List

def bot_of_mem_either [DecidableEq F] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ⊥ := by
  have hp : Γ ⊢[𝓢]! φ := FiniteContext.byAxm h₁;
  have hnp : Γ ⊢[𝓢]! φ 🡒 ⊥ := CO_of_N $ FiniteContext.byAxm h₂;
  exact hnp ⨀ hp

def negMDP (hnp : 𝓢 ⊢! ∼φ) (hn : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊥ := (CO_of_N hnp) ⨀ hn
lemma neg_mdp (hnp : 𝓢 ⊢ ∼φ) (hn : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊥ := ⟨negMDP hnp.some hn.some⟩

def K_replace_left (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! φ 🡒 χ) : 𝓢 ⊢! χ ⋏ ψ := K_intro (h ⨀ K_left hc) (K_right hc)

def K_replace_right (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! ψ 🡒 χ) : 𝓢 ⊢! φ ⋏ χ := K_intro (K_left hc) (h ⨀ K_right hc)

def K_replace (hc : 𝓢 ⊢! φ ⋏ ψ) (h₁ : 𝓢 ⊢! φ 🡒 χ) (h₂ : 𝓢 ⊢! ψ 🡒 ξ) : 𝓢 ⊢! χ ⋏ ξ := K_replace_right (K_replace_left hc h₁) h₂

def CKK_of_C_of_C (h₁ : 𝓢 ⊢! φ 🡒 χ) (h₂ : 𝓢 ⊢! ψ 🡒 ξ) : 𝓢 ⊢! φ ⋏ ψ 🡒 χ ⋏ ξ := by
  apply deduct';
  exact K_replace FiniteContext.id (of h₁) (of h₂)

end
end Entailment
end LO
end

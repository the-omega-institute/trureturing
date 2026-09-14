/- GID: D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentFour
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Propositional.Entailment.Minimal for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcEntailment.EntailmentTwo
public import D5.S3.ConceptDynamics.ZfcFiniteCollections.Finset
public import D5.S3.ConceptDynamics.ZfcMinimalLogic.MinimalEntailmentThree

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Propositional/Entailment/Minimal.lean, original lines 960-1272.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section
namespace LO
namespace Entailment
section
variable {F : Type*} [LogicalConnective F] [LogicalNeutral F]
         {S : Type*} [Entailment S F]
         {𝓢 : S} [Entailment.Minimal 𝓢]
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}
open NegationEquiv
open FiniteContext
open List

def EKK_of_E_of_E (hp : 𝓢 ⊢! φ₁ 🡘 φ₂) (hq : 𝓢 ⊢! ψ₁ 🡘 ψ₂) : 𝓢 ⊢! φ₁ ⋏ ψ₁ 🡘 φ₂ ⋏ ψ₂ := by
  apply E_intro;
  . exact CKK_of_C_of_C (K_left hp) (K_left hq);
  . exact CKK_of_C_of_C (K_right hp) (K_right hq);

def dni [DecidableEq F] : 𝓢 ⊢! φ 🡒 ∼∼φ := by
  apply deduct';
  apply N_of_CO;
  apply deduct;
  exact bot_of_mem_either (φ := φ) (by simp) (by simp);

def dni' [DecidableEq F] (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼∼φ := dni ⨀ b

def CNNOO : 𝓢 ⊢! ∼∼⊥ 🡒 ⊥ := by
  apply deduct'
  have d₁ : [∼∼⊥] ⊢[𝓢]! ∼⊥ 🡒 ⊥ := CO_of_N byAxm₀
  have d₂ : [∼∼⊥] ⊢[𝓢]! ∼⊥ := N_of_CO C_id
  exact d₁ ⨀ d₂

def ENNOO [DecidableEq F] : 𝓢 ⊢! ∼∼⊥ 🡘 ⊥ := K_intro CNNOO dni

def CCCNN [DecidableEq F] : 𝓢 ⊢! (φ 🡒 ψ) 🡒 (∼ψ 🡒 ∼φ) := by
  apply deduct';
  apply deduct;
  apply N_of_CO;
  apply deduct;
  have dp  : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢]! φ := FiniteContext.byAxm;
  have dpq : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢]! φ 🡒 ψ := FiniteContext.byAxm;
  have dq  : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢]! ψ := dpq ⨀ dp;
  have dnq : [φ, ∼ψ, φ 🡒 ψ] ⊢[𝓢]! ψ 🡒 ⊥ := CO_of_N $ FiniteContext.byAxm;
  exact dnq ⨀ dq;

def contra [DecidableEq F] (b : 𝓢 ⊢! φ 🡒 ψ) : 𝓢 ⊢! ∼ψ 🡒 ∼φ := CCCNN ⨀ b

def ENN_of_E [DecidableEq F] (b : 𝓢 ⊢! φ 🡘 ψ) : 𝓢 ⊢! ∼φ 🡘 ∼ψ := E_intro (contra $ K_right b) (contra $ K_left b)

section NegationEquiv

end NegationEquiv

def tne [DecidableEq F] : 𝓢 ⊢! ∼(∼∼φ) 🡒 ∼φ := contra dni

def tneIff [DecidableEq F] : 𝓢 ⊢! ∼∼∼φ 🡘 ∼φ := K_intro tne dni

def C_swap [DecidableEq F] (h : 𝓢 ⊢! φ 🡒 ψ 🡒 χ) : 𝓢 ⊢! ψ 🡒 φ 🡒 χ := by
  apply deduct';
  apply deduct;
  exact (of (Γ := [φ, ψ]) h) ⨀ FiniteContext.byAxm ⨀ FiniteContext.byAxm;

def CNAKNN [DecidableEq F] : 𝓢 ⊢! ∼(φ ⋎ ψ) 🡒 (∼φ ⋏ ∼ψ) := by
  apply deduct';
  exact K_intro (deductInv $ contra $ or₁) (deductInv $ contra $ or₂)

def KNN_of_NA [DecidableEq F] (b : 𝓢 ⊢! ∼(φ ⋎ ψ)) : 𝓢 ⊢! ∼φ ⋏ ∼ψ := CNAKNN ⨀ b

section Conjunction

end Conjunction
end
end Entailment
end LO
end

/- GID: D5/S3/ConceptDynamics/ZfcPropositional/ClEntailment
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcPropositional/ClEntailment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Propositional.Entailment.Cl for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcPropositional.IntEntailmentTwo

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Propositional/Entailment/Cl.lean, original lines 1-350.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev DNE := ∼∼φ 🡒 φ

protected abbrev LEM := φ ⋎ ∼φ

end LO.Axioms

namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomDNE (𝓢 : S)  where
  dne {φ : F} : 𝓢 ⊢! Axioms.DNE φ
export HasAxiomDNE (dne)

def of_NN [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼∼φ) : 𝓢 ⊢! φ := dne ⨀ b
@[grind ⇒] lemma of_NN! [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ ∼∼φ) : 𝓢 ⊢ φ := ⟨of_NN h.some⟩

section

variable [LogicalNeutral F] [Entailment.Minimal 𝓢]

namespace FiniteContext

end FiniteContext

namespace Context

end Context

end

class HasAxiomLEM (𝓢 : S)  where
  lem {φ : F} : 𝓢 ⊢! Axioms.LEM φ
export HasAxiomLEM (lem)

@[simp] lemma lem! [HasAxiomLEM 𝓢] : 𝓢 ⊢ φ ⋎ ∼φ := ⟨lem⟩

section

variable [LogicalNeutral F] [Entailment.Minimal 𝓢]

namespace FiniteContext

end FiniteContext

namespace Context

end Context

end

section

variable [LogicalNeutral F] [Entailment.Minimal 𝓢]

namespace FiniteContext

end FiniteContext

namespace Context

end Context

end

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F]
         {S : Type*} [Entailment S F]
         {𝓢 : S}
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}

protected class Cl (𝓢 : S) extends Entailment.Minimal 𝓢, Entailment.HasAxiomDNE 𝓢

variable [Entailment.Cl 𝓢]

namespace FiniteContext

end FiniteContext

namespace Context

end Context

open NegationEquiv
open FiniteContext
open List

def A_of_ANNNN (d : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢! φ ⋎ ψ := of_C_of_C_of_A (C_trans dne or₁) (C_trans dne or₂) d

def CN_of_CN_left (b : 𝓢 ⊢! ∼φ 🡒 ψ) : 𝓢 ⊢! ∼ψ 🡒 φ := C_trans (contra b) dne

def C_of_CNN (b : 𝓢 ⊢! ∼φ 🡒 ∼ψ) : 𝓢 ⊢! ψ 🡒 φ := C_trans dni (CN_of_CN_left b)

def AN_of_C (d : 𝓢 ⊢! φ 🡒 ψ) : 𝓢 ⊢! ∼φ ⋎ ψ := by
  apply of_NN;
  apply N_of_CO;
  apply deduct';
  have d₁ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼∼φ ⋏ ∼ψ := KNN_of_NA $ FiniteContext.id;
  have d₂ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼φ 🡒 ⊥ := CO_of_N $ K_left d₁;
  have d₃ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼φ := (of (Γ := [∼(∼φ ⋎ ψ)]) $ contra d) ⨀ (K_right d₁);
  exact d₂ ⨀ d₃;

instance : HasAxiomEFQ 𝓢 where
  efq {φ} := by
    apply C_of_CNN;
    exact C_trans (K_left negEquiv) $ C_trans (C_swap implyK) (K_right negEquiv);

instance : Entailment.Int 𝓢 where

instance : HasAxiomLEM 𝓢 := ⟨A_of_ANNNN $ AN_of_C dni⟩

section

end

section consistency

omit [Entailment.Cl 𝓢]

variable [AdjunctiveSet F S] [Axiomatized S] [Deduction S] [∀ 𝓢 : S, Entailment.Cl 𝓢]

lemma provable_iff_inconsistent_adjoin {φ : F} :
    𝓢 ⊢ φ ↔ Inconsistent (adjoin (∼φ) 𝓢) := by
  constructor
  · intro h
    apply inconsistent_of_provable_of_unprovable (φ := φ)
    · exact Axiomatized.to_adjoin h
    · exact Axiomatized.adjoin! _ _
  · intro h
    have : 𝓢 ⊢ ∼φ 🡒 ⊥ := Deduction.of_insert! (h _)
    refine of_NN! <| N!_iff_CO!.mpr this

lemma unprovable_iff_consistent_adjoin {φ : F} :
    𝓢 ⊬ φ ↔ Consistent (adjoin (∼φ) 𝓢) := by
  simpa using provable_iff_inconsistent_adjoin.not

end consistency

section

end

section

variable {G T : Type*} [Entailment T G] [LogicalConnective G] [LogicalNeutral G] {𝓣 : T}

end

section

variable {S F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F] [Entailment S F]
         {𝓢 : S} [Entailment.Int 𝓢]

open FiniteContext

end

end LO.Entailment

end

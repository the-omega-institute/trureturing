/- GID: D5/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentTwo
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcMinimalLogic/MinimalEntailmentTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Propositional.Entailment.Minimal for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcEntailment.EntailmentTwo
public import D5.S3.ConceptDynamics.ZfcFiniteCollections.Finset
public import D5.S3.ConceptDynamics.ZfcMinimalLogic.MinimalEntailmentOne

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Propositional/Entailment/Minimal.lean, original lines 321-639.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section
namespace LO
namespace Entailment
section
variable {S F : Type*} [LogicalConnective F] [LogicalNeutral F] [Entailment S F]
variable {𝓢 : S} [Entailment.Minimal 𝓢] {φ ψ χ : F}

variable {Γ Δ : List F}

def conj₂Nth : (Γ : List F) → (n : ℕ) → (hn : n < Γ.length) → 𝓢 ⊢! ⋀Γ 🡒 Γ[n]
  |          [],     _, hn => by simp at hn
  |         [ψ],     0, _  => C_id
  | φ :: ψ :: Γ,     0, _  => and₁
  | φ :: ψ :: Γ, n + 1, hn => C_trans (and₂ (φ := φ)) (conj₂Nth (ψ :: Γ) n (Nat.succ_lt_succ_iff.mp hn))

def left_Conj₂_intro [DecidableEq F] {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢! ⋀Γ 🡒 φ :=
  have : Γ.idxOf φ < Γ.length := List.idxOf_lt_length_of_mem h
  cast <| conj₂Nth Γ (Γ.idxOf φ) (by assumption)

def Conj₂_intro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢! φ) : 𝓢 ⊢! ⋀Γ :=
  match Γ with
  |          [] => verum
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by exact K_intro (b ψ (by simp)) (Conj₂_intro _ (by aesop))
lemma Conj₂!_intro (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ ⋀Γ := ⟨Conj₂_intro Γ (λ φ hp => (b φ hp).some)⟩

def right_Conj₂_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ 🡒 ψ) : 𝓢 ⊢! φ 🡒 ⋀Γ :=
  match Γ with
  |          [] => C_of_conseq verum
  |         [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by apply CK_of_C_of_C (b ψ (by simp)) (right_Conj₂_intro φ _ (fun ψ hq ↦ b ψ (by simp [hq])));

def CConj₂Conj₂ [DecidableEq F] {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢! ⋀Γ 🡒 ⋀Δ :=
  right_Conj₂_intro _ _ (fun _ hq ↦ left_Conj₂_intro (h hq))

section

variable {G T : Type*} [Entailment T G] [LogicalConnective G] [LogicalNeutral G] {𝓣 : T}

end

end

section

structure FiniteContext (F) (𝓢 : S) where
  ctx : List F

namespace FiniteContext

variable {F} {S} {𝓢 : S}

instance : Coe (List F) (FiniteContext F 𝓢) := ⟨mk⟩

abbrev conj [LogicalConnective F] [LogicalNeutral F] (Γ : FiniteContext F 𝓢) : F := ⋀Γ.ctx

instance : EmptyCollection (FiniteContext F 𝓢) := ⟨⟨[]⟩⟩

instance : Membership F (FiniteContext F 𝓢) := ⟨λ Γ x => (x ∈ Γ.ctx)⟩

instance : HasSubset (FiniteContext F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Adjoin F (FiniteContext F 𝓢) := ⟨(· :: ·.ctx)⟩

lemma mem_def {φ : F} {Γ : FiniteContext F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx := iff_of_eq rfl

@[simp] lemma coe_subset_coe_iff {Γ Δ : List F} : (Γ : FiniteContext F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ := iff_of_eq rfl

@[simp] lemma mem_coe_iff {φ : F} {Γ : List F} : φ ∈ (Γ : FiniteContext F 𝓢) ↔ φ ∈ Γ := iff_of_eq rfl

@[simp] lemma not_mem_empty (φ : F) : ¬φ ∈ (∅ : FiniteContext F 𝓢) := by simp [EmptyCollection.emptyCollection]

instance : AdjunctiveSet F (FiniteContext F 𝓢) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin, mem_def]

variable [Entailment S F] [LogicalConnective F] [LogicalNeutral F]

instance (𝓢 : S) : Entailment (FiniteContext F 𝓢) F := ⟨(𝓢 ⊢! ·.conj 🡒 ·)⟩

abbrev Prf (𝓢 : S) (Γ : List F) (φ : F) : Type _ := (Γ : FiniteContext F 𝓢) ⊢! φ

notation Γ:45 " ⊢[" 𝓢 "]! " φ:46 => Prf 𝓢 Γ φ

def ofDef {Γ : List F} {φ : F} (b : 𝓢 ⊢! ⋀Γ 🡒 φ) : Γ ⊢[𝓢]! φ := b

def toDef {Γ : List F} {φ : F} (b : Γ ⊢[𝓢]! φ) : 𝓢 ⊢! ⋀Γ 🡒 φ := b

def cast {Γ φ} (d : Γ ⊢[𝓢]! φ) (eΓ : Γ = Γ') (eφ : φ = φ') : Γ' ⊢[𝓢]! φ' := eΓ ▸ eφ ▸ d

section

variable {Γ Δ E : List F}
variable [Entailment.Minimal 𝓢]

instance [DecidableEq F] : Axiomatized (FiniteContext F 𝓢) where
  prfAxm := fun hp ↦ left_Conj₂_intro hp
  weakening := fun H b ↦ C_trans (CConj₂Conj₂ H) b

def nthAxm {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢]! Γ[n] := conj₂Nth Γ n h

def byAxm [DecidableEq F] {φ} (h : φ ∈ Γ := by simp) : Γ ⊢[𝓢]! φ := Axiomatized.prfAxm (by simpa)

def weakening [DecidableEq F] (h : Γ ⊆ Δ) {φ} : Γ ⊢[𝓢]! φ → Δ ⊢[𝓢]! φ := Axiomatized.weakening (by simpa)

def of {φ : F} (b : 𝓢 ⊢! φ) : Γ ⊢[𝓢]! φ := C_of_conseq (ψ := ⋀Γ) b

def emptyPrf {φ : F} : [] ⊢[𝓢]! φ → 𝓢 ⊢! φ := fun b ↦ b ⨀ verum

def id : [φ] ⊢[𝓢]! φ := nthAxm 0

def byAxm₀ : (φ :: Γ) ⊢[𝓢]! φ := nthAxm 0

def byAxm₁ : (φ :: ψ :: Γ) ⊢[𝓢]! ψ := nthAxm 1

def byAxm₂ : (φ :: ψ :: χ :: Γ) ⊢[𝓢]! χ := nthAxm 2

instance (Γ : FiniteContext F 𝓢) : Entailment.ModusPonens Γ := ⟨mdp₁⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomVerum Γ := ⟨of verum⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImplyK Γ := ⟨of implyK⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImplyS Γ := ⟨of implyS⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndElim Γ := ⟨of and₁, of and₂⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndInst Γ := ⟨of and₃⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrInst Γ := ⟨of or₁, of or₂⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrElim Γ := ⟨of or₃⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.NegationEquiv Γ := ⟨of negEquiv⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.Minimal Γ where

def deduct {φ ψ : F} : {Γ : List F} → (φ :: Γ) ⊢[𝓢]! ψ → Γ ⊢[𝓢]! φ 🡒 ψ
  | .nil => fun b ↦ ofDef <| C_of_conseq (toDef b)
  | .cons _ _ => fun b ↦ ofDef <| CC_of_CK (C_trans CKK (toDef b))

def deductInv {φ ψ : F} : {Γ : List F} → Γ ⊢[𝓢]! φ 🡒 ψ → (φ :: Γ) ⊢[𝓢]! ψ
  | .nil => λ b => ofDef <| (toDef b) ⨀ verum
  | .cons _ _ => λ b => ofDef <| (C_trans CKK (CK_of_CC (toDef b)))

def deduct' : [φ] ⊢[𝓢]! ψ → 𝓢 ⊢! φ 🡒 ψ := fun b ↦ emptyPrf <| deduct b

end

end FiniteContext

variable (F)

structure Context (𝓢 : S) where
  ctx : Set F

variable {F}

namespace Context

variable {𝓢 : S}

instance : Coe (Set F) (Context F 𝓢) := ⟨mk⟩

instance : Membership F (Context F 𝓢) := ⟨λ Γ x => (x ∈ Γ.ctx)⟩

@[simp] lemma mem_coe_iff {φ : F} {Γ : Set F} : φ ∈ (Γ : Context F 𝓢) ↔ φ ∈ Γ := iff_of_eq rfl

variable [LogicalConnective F] [LogicalNeutral F] [Entailment S F]

structure Proof (Γ : Context F 𝓢) (φ : F) where
  ctx : List F
  subset : ∀ ψ ∈ ctx, ψ ∈ Γ
  prf : ctx ⊢[𝓢]! φ

instance (𝓢 : S) : Entailment (Context F 𝓢) F := ⟨Proof⟩

variable (𝓢)

abbrev Prf (Γ : Set F) (φ : F) : Type _ := (Γ : Context F 𝓢) ⊢! φ

abbrev Provable (Γ : Set F) (φ : F) : Prop := (Γ : Context F 𝓢) ⊢ φ

end Context
end
end Entailment
end LO
end

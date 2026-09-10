/- GID: D5/S3/ConceptDynamics/ZfcLogic/Semantics
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcLogic/Semantics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logic.Semantics for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcFiniteCollections.List
public import D5.S3.ConceptDynamics.ZfcLanguageSupport.NotationClass
public import D5.S3.ConceptDynamics.ZfcLogic.LogicSymbolTwo

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Logic/Semantics.lean, selected commands within original lines 1-363.
   Selection excludes the optional Semantics.Top (Set M) instance at original line 251.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO

/-- `Semantics M F` denotes semantics of formulae `F for models `M` -/
class Semantics (M : Type*) (F : outParam Type*) where
  Models : M → F → Prop

variable {M : Type*} {F : Type*} [𝓢 : Semantics M F]

namespace Semantics

infix:45 " ⊧ " => Models

/-- The negation of `𝓜 ⊧ φ` -/
abbrev NotModels (𝓜 : M) (φ : F) : Prop := ¬𝓜 ⊧ φ

infix:45 " ⊭ " => NotModels

section

variable [LogicalConnective F] [LogicalNeutral F] (M)

/-- Tarski's truth definition for `⊤`. -/
protected class Top where
  models_verum (𝓜 : M) : 𝓜 ⊧ (⊤ : F)

/-- Tarski's truth definition for `⊥`. -/
protected class Bot where
  models_falsum (𝓜 : M) : ¬𝓜 ⊧ (⊥ : F)

/-- Tarski's truth definition for `⋏`. -/
protected class And where
  models_and {𝓜 : M} {φ ψ : F} : 𝓜 ⊧ φ ⋏ ψ ↔ 𝓜 ⊧ φ ∧ 𝓜 ⊧ ψ

/-- Tarski's truth definition for `⋎`. -/
protected class Or where
  models_or {𝓜 : M} {φ ψ : F} : 𝓜 ⊧ φ ⋎ ψ ↔ 𝓜 ⊧ φ ∨ 𝓜 ⊧ ψ

/-- Tarski's truth definition for `🡒`. -/
protected class Imp where
  models_imply {𝓜 : M} {φ ψ : F} : 𝓜 ⊧ φ 🡒 ψ ↔ (𝓜 ⊧ φ → 𝓜 ⊧ ψ)

/-- Tarski's truth definition for `∼`. -/
protected class Not where
  models_not {𝓜 : M} {φ : F} : 𝓜 ⊧ ∼φ ↔ ¬𝓜 ⊧ φ

/-- Tarski's truth definitions. -/
class Tarski extends
  Semantics.Top M,
  Semantics.Bot M,
  Semantics.And M,
  Semantics.Or M,
  Semantics.Imp M,
  Semantics.Not M
  where

attribute [simp, grind .]
  Top.models_verum
  Bot.models_falsum

attribute [simp, grind =]
  Not.models_not
  And.models_and
  Or.models_or
  Imp.models_imply

variable {M}

variable [Tarski M]

variable {𝓜 : M}

@[simp] lemma models_iff {φ ψ : F} :
    𝓜 ⊧ φ 🡘 ψ ↔ (𝓜 ⊧ φ ↔ 𝓜 ⊧ ψ) := by
  simp [LogicalConnective.iff, iff_iff_implies_and_implies]

@[simp] lemma models_list_conj₂ {l : List F} :
    𝓜 ⊧ ⋀l ↔ ∀ φ ∈ l, 𝓜 ⊧ φ := by induction l using List.induction_with_singleton <;> simp [*]

end

/-- `𝓜 ⊧* T` denotes `𝓜 ⊧ φ` for all `φ` in `T`. -/
class ModelsSet (𝓜 : M) (T : Set F) : Prop where
  models_set : ∀ ⦃φ⦄, φ ∈ T → Models 𝓜 φ

infix:45 " ⊧* " => ModelsSet

variable (M)

def Satisfiable (T : Set F) : Prop := ∃ 𝓜 : M, 𝓜 ⊧* T

/-- A set of models satisfies set of formulae `T`. -/
def models (T : Set F) : Set M := {𝓜 | 𝓜 ⊧* T}

variable {M}

class Meaningful (𝓜 : M) : Prop where
  exists_unmodels : ∃ φ, 𝓜 ⊭ φ

instance [LogicalNeutral F] [Semantics.Bot M] (𝓜 : M) : Meaningful 𝓜 := ⟨⟨⊥, by grind⟩⟩

lemma modelsSet_iff {𝓜 : M} {T : Set F} : 𝓜 ⊧* T ↔ ∀ ⦃φ⦄, φ ∈ T → Models 𝓜 φ :=
  ⟨by rintro ⟨h⟩ φ hf; exact h hf, by intro h; exact ⟨h⟩⟩

@[simp] lemma satisfiable_conj₂ [LogicalConnective F] [LogicalNeutral F] [Tarski M] [DecidableEq F] (l : List F) :
    Satisfiable M {⋀l} ↔ Satisfiable M {φ | φ ∈ l} := by
  simp [Satisfiable, modelsSet_iff]

lemma satisfiableSet_iff_models_nonempty {T : Set F} :
    Satisfiable M T ↔ (models M T).Nonempty :=
  ⟨by rintro ⟨𝓜, h𝓜⟩; exact ⟨𝓜, h𝓜⟩, by rintro ⟨𝓜, h𝓜⟩; exact ⟨𝓜, h𝓜⟩⟩

namespace ModelsSet

lemma models {T : Set F} (𝓜 : M) [𝓜 ⊧* T] (hf : φ ∈ T) : 𝓜 ⊧ φ :=
  models_set hf

lemma of_subset {T U : Set F} {𝓜 : M} (h : 𝓜 ⊧* U) (ss : T ⊆ U) : 𝓜 ⊧* T :=
  ⟨fun _ hf => h.models_set (ss hf)⟩

@[simp] lemma singleton_iff {φ : F} {𝓜 : M} :
    𝓜 ⊧* {φ} ↔ 𝓜 ⊧ φ := by simp [modelsSet_iff]

@[simp] lemma insert_iff {T : Set F} {φ : F} {𝓜 : M} :
    𝓜 ⊧* insert φ T ↔ 𝓜 ⊧ φ ∧ 𝓜 ⊧* T := by
  simp [modelsSet_iff]

@[simp] lemma image_iff {ι} {φ : ι → F} {A : Set ι} {𝓜 : M} :
    𝓜 ⊧* φ '' A ↔ ∀ i ∈ A, 𝓜 ⊧ φ i := by simp [modelsSet_iff]

end ModelsSet

lemma Satisfiable.of_subset {T U : Set F} (h : Satisfiable M U) (ss : T ⊆ U) : Satisfiable M T := by
  rcases h with ⟨𝓜, h⟩; exact ⟨𝓜, ModelsSet.of_subset h ss⟩

variable (M)

instance : Semantics (Set M) F := ⟨fun s φ ↦ ∀ ⦃𝓜⦄, 𝓜 ∈ s → 𝓜 ⊧ φ⟩

@[simp] lemma empty_models (φ : F) : (∅ : Set M) ⊧ φ := by rintro h; simp

/-- The logical conseqence. -/
def Consequence (T : Set F) (φ : F) : Prop := models M T ⊧ φ

-- note that ⊨ (\vDash) is *NOT* ⊧ (\models)
notation T:45 " ⊨[" M "] " φ:46 => Consequence M T φ

variable {M}

lemma set_models_iff {s : Set M} : s ⊧ φ ↔ ∀ 𝓜 ∈ s, 𝓜 ⊧ φ := iff_of_eq rfl


lemma set_meaningful_iff_nonempty [∀ 𝓜 : M, Meaningful 𝓜] {s : Set M} : Meaningful s ↔ s.Nonempty := by
  constructor;
  . rintro ⟨φ, hf⟩;
    by_contra A;
    rcases Set.not_nonempty_iff_eq_empty.mp A; simp [NotModels] at hf;
  . rintro ⟨𝓜, h𝓜⟩;
    rcases Meaningful.exists_unmodels (self := by tauto) with ⟨φ, hf⟩;
    exact ⟨φ, by simpa [NotModels, set_models_iff] using ⟨𝓜, h𝓜, hf⟩⟩

lemma meaningful_iff_satisfiableSet [∀ 𝓜 : M, Meaningful 𝓜] : Satisfiable M T ↔ Meaningful (models M T) := by
  simp [set_meaningful_iff_nonempty, satisfiableSet_iff_models_nonempty]

end Semantics

namespace Cumulative

end Cumulative

variable (M)

variable {M}

namespace Compact

end Compact

end LO

end

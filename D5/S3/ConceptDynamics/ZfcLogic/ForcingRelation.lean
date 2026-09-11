/- GID: D5/S3/ConceptDynamics/ZfcLogic/ForcingRelation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcLogic/ForcingRelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logic.ForcingRelation for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcFiniteCollections.List
public import D5.S3.ConceptDynamics.ZfcLanguageSupport.NotationClass
public import D5.S3.ConceptDynamics.ZfcLogic.LogicSymbolTwo
public import D5.S3.ConceptDynamics.ZfcSupport.AdjunctiveSet

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Logic/ForcingRelation.lean, original lines 1-155.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO

class ForcingRelation (W : Type*) (F : outParam Type*) where
  Forces : W → F → Prop

infix:45 " ⊩ " => ForcingRelation.Forces

namespace ForcingRelation

variable {W : Type*} {F : Type*} [ForcingRelation W F] [LogicalConnective F] [LogicalNeutral F]

variable (W)

class BasicSemantics where
  verum (w : W) : w ⊩ ⊤
  and (w : W) : w ⊩ φ ⋏ ψ ↔ w ⊩ φ ∧ w ⊩ ψ
  or (w : W) : w ⊩ φ ⋎ ψ ↔ w ⊩ φ ∨ w ⊩ ψ

class Monotone (R : outParam (W → W → Prop)) where
  monotone {w : W} : w ⊩ φ → ∀ v, R w v → v ⊩ φ

class IntKripke (R : outParam (W → W → Prop)) extends BasicSemantics W, Monotone W R where
  imply (w : W) : w ⊩ φ 🡒 ψ ↔ (∀ v, R w v → v ⊩ φ → v ⊩ ψ)
  falsum (w : W) : ¬w ⊩ ⊥
  not (w : W) : w ⊩ ∼φ ↔ (∀ v, R w v → ¬v ⊩ φ)

variable {W}

attribute [simp, grind .]
  BasicSemantics.verum BasicSemantics.and
  BasicSemantics.or
  IntKripke.falsum

attribute [grind .]
  IntKripke.imply
  IntKripke.not

@[simp, grind =]
lemma iff (R : W → W → Prop) [IntKripke W R] : w ⊩ (φ 🡘 ψ) ↔ (∀ v, R w v → (v ⊩ φ ↔ v ⊩ ψ)) := by
  simp [LogicalConnective.iff, IntKripke.imply]; grind

variable (W)

abbrev AllForces (φ : F) : Prop := ∀ w : W, w ⊩ φ

infix:45 " ∀⊩ " => AllForces

variable {W}

namespace AllForces

end AllForces

end ForcingRelation

class WeakForcingRelation (ℙ : Type*) (F : outParam Type*) where
  WeaklyForces : ℙ → F → Prop

infix:45 " ⊩ᶜ " => WeakForcingRelation.WeaklyForces

namespace WeakForcingRelation

variable {ℙ : Type*} {F : Type*} [WeakForcingRelation ℙ F] [LogicalConnective F] [LogicalNeutral F]

variable (ℙ)

variable {ℙ}

variable (ℙ)

abbrev AllForces (φ : F) : Prop := ∀ p : ℙ, p ⊩ᶜ φ

infix:45 " ∀⊩ᶜ " => AllForces

variable {ℙ}

namespace AllForces

/-
@[simp] lemma or [ClassicalKripke ℙ R] : ℙ ∀⊩ᶜ φ ⋎ ψ ↔ ℙ ∀⊩ᶜ φ ∨ ℙ ∀⊩ᶜ ψ := by
  simp [AllForces]
  constructor
  · intro h
    by_contra! C
    rcases C with ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
-/

end AllForces

end WeakForcingRelation

end LO

end

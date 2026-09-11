/- GID: D5/S3/ConceptDynamics/ZfcEntailment/CalculusTwo
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcEntailment/CalculusTwo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logic.Calculus for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcPropositional.ClEntailment
public import D5.S3.ConceptDynamics.ZfcEntailment.CalculusOne

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Logic/Calculus.lean, original lines 321-376.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose]
public section
namespace LO
namespace OneSidedLK
variable {F : Type*} [LogicalConnective F] [LogicalNeutral F]
  [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] {𝔇 : List F → Type*}
open Entailment
namespace ContextualEntailment
variable {S : Type*} [Entailment S F] [AdjunctiveSet F S] [ContextualEntailment 𝔇 S]
variable [OneSidedLK.Cut 𝔇]

variable {P : Type*} [Entailment P F]

lemma iff_context {𝓢 : S} {𝓟 : P} [PrincipalEntailment 𝔇 𝓟] :
    𝓢 ⊢ φ ↔ AdjunctiveSet.set 𝓢 *⊢[𝓟] φ := by
  constructor
  · rintro h
    have ⟨Γ, hΓ, ⟨d⟩⟩ := provable_iff.mp h
    have : 𝓟 ⊢ ⋀Γ 🡒 φ := by
      have : 𝔇 (∼Γ ++ [φ]) := contra d
      have : Nonempty (𝔇 [⋀Γ 🡒 φ]) := by simpa [LogicalConnective.DeMorgan.imply] using Nonempty.intro (or <| disj₂ this)
      exact PrincipalEntailment.provable_iff.mpr this
    refine ⟨⟨Γ, by simpa using hΓ, this.some⟩⟩
  · rintro ⟨Γ, h, d⟩
    have : 𝓟 ⊢! ⋀Γ 🡒 φ := d
    have d : 𝔇 [⋁(∼Γ) ⋎ φ] := cast (PrincipalEntailment.equiv this) (by simp [LogicalConnective.DeMorgan.imply])
    have : 𝔇 (⋀Γ ⋏ ∼φ :: φ :: ∼Γ) :=
      have : 𝔇 (⋀Γ :: ∼Γ) := conj₂ fun φ h ↦ close φ (by simp) (by simp [h])
      contra <| tensor this (rotate <| identity φ)
    have : 𝔇 (φ :: ∼Γ) := eCut d this
    refine provable_iff.mpr ⟨Γ, h, ⟨this⟩⟩

lemma of_principal_provable {𝓟 : P} [PrincipalEntailment 𝔇 𝓟] {𝓢 : S} : 𝓟 ⊢ φ → 𝓢 ⊢ φ := fun h ↦
  iff_context.mpr (Entailment.Context.of! h)

open Classical in
noncomputable abbrev deduction (𝓟 : P) [PrincipalEntailment 𝔇 𝓟] : Entailment.Deduction S where
  ofInsert {φ ψ 𝓢 b} :=
    have : AdjunctiveSet.set (Adjoin.adjoin φ 𝓢) *⊢[𝓟] ψ := iff_context.mp ⟨b⟩
    have : AdjunctiveSet.set 𝓢 *⊢[𝓟] φ 🡒 ψ := Context.deduct! <| by simpa using this
    (iff_context.mpr this).get
  inv {φ ψ 𝓢 b} :=
    have : AdjunctiveSet.set (Adjoin.adjoin φ 𝓢) *⊢[𝓟] ψ := by simpa using Context.deductInv! (iff_context.mp ⟨b⟩)
    (iff_context.mpr this).get

end ContextualEntailment

end OneSidedLK

end LO

end

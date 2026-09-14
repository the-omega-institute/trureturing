/- GID: D5/S3/ConceptDynamics/ZfcEntailment/CalculusOne
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcEntailment/CalculusOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logic.Calculus for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcPropositional.ClEntailment

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Logic/Calculus.lean, original lines 1-320.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose]
public section

namespace LO

class OneSidedLK {F : Type*} [LogicalConnective F] [LogicalNeutral F]
    [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] (𝔇 : List F → Type*) where
  identity (φ) : 𝔇 [φ, ∼φ]
  contraction : 𝔇 Δ → Δ ⊆ Γ → 𝔇 Γ
  verum : 𝔇 [⊤]
  and : 𝔇 (φ :: Γ) → 𝔇 (ψ :: Γ) → 𝔇 (φ ⋏ ψ :: Γ)
  or : 𝔇 (φ :: ψ :: Γ) → 𝔇 (φ ⋎ ψ :: Γ)

class OneSidedLK.Cut
    {F : Type*} [LogicalConnective F] [LogicalNeutral F]
    [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] (𝔇 : List F → Type*) extends OneSidedLK 𝔇 where
  cut : 𝔇 (φ :: Γ) → 𝔇 (∼φ :: Δ) → 𝔇 (Γ ++ Δ)

namespace OneSidedLK

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F]
  [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] {𝔇 : List F → Type*}

def cast (b : 𝔇 Γ) (h : Γ = Δ := by simp) : 𝔇 Δ := h ▸ b

def contra [OneSidedLK 𝔇] (d : 𝔇 Γ) (h : Γ ⊆ Δ := by simp) : 𝔇 Δ := contraction d (by simp [h])

def rotate [OneSidedLK 𝔇] (d : 𝔇 (φ :: Γ)) : 𝔇 (Γ ++ [φ]) := contra d

def close [OneSidedLK 𝔇] (φ : F) (hp : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : 𝔇 Γ := contraction (identity φ) (by simp_all)

def top [OneSidedLK 𝔇] (h : ⊤ ∈ Γ := by simp) : 𝔇 Γ := contraction verum (by simp [h])

def tensor [OneSidedLK 𝔇] {φ ψ : F} (dφ : 𝔇 (φ :: Γ)) (dψ : 𝔇 (ψ :: Δ)) : 𝔇 (φ ⋏ ψ :: Γ ++ Δ) :=
  and (contraction dφ (by simp)) (contraction dψ (by simp))

def swap₁ [OneSidedLK 𝔇] (d : 𝔇 (φ₂ :: φ₁ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: Γ) := contraction d (by simp)

def swap₂ [OneSidedLK 𝔇] (d : 𝔇 (φ₃ :: φ₁ :: φ₂ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: φ₃ :: Γ) :=
  contraction d (by grind)

def swap₃ [OneSidedLK 𝔇] (d : 𝔇 (φ₄ :: φ₁ :: φ₂ :: φ₃ :: Γ)) : 𝔇 (φ₁ :: φ₂ :: φ₃ :: φ₄ :: Γ) :=
  contraction d (by grind)

alias cut := OneSidedLK.Cut.cut

def eCut [Cut 𝔇] (d₁ : 𝔇 (φ :: Γ)) (d₂ : 𝔇 (ψ :: Δ)) (e : ∼φ = ψ := by simp) : 𝔇 (Γ ++ Δ) := cut d₁ (cast d₂ (by simp [e]))

def disj₂ {Γ Δ : List F} [Cut 𝔇] : 𝔇 (Γ ++ Δ) → 𝔇 (⋁Γ :: Δ) := fun d ↦
  match Γ with
  |               [] => contra d
  |              [φ] => d
  |           [φ, ψ] => or d
  | φ :: ψ :: χ :: Γ => by
    let Φ := ⋁(χ :: Γ)
    have : 𝔇 ((φ ⋎ ψ :: χ :: Γ) ++ Δ) := or d
    have d₁ : 𝔇 ((φ ⋎ ψ) ⋎ Φ :: Δ) := disj₂ this
    have d₂ : 𝔇 [(∼φ ⋏ ∼ψ) ⋏ ∼Φ, φ ⋎ ψ ⋎ Φ] :=
      have : 𝔇 [φ, ψ ⋎ Φ, (∼φ ⋏ ∼ψ) ⋏ ∼Φ] :=
        contra <| or <| rotate <| rotate <|
          tensor (tensor (rotate (identity (𝔇 := 𝔇) φ)) (rotate (identity  ψ))) (rotate (identity Φ))
      rotate <| or <| this
    exact eCut d₂ d₁
  termination_by _ => Γ.length

def conj₂ [OneSidedLK 𝔇] {Γ Δ : List F} (d : (φ : F) → φ ∈ Γ → 𝔇 (φ :: Δ)) : 𝔇 (⋀Γ :: Δ) :=
  match Γ with
  |          [] => contra verum
  |         [φ] => d φ (by simp)
  | φ :: ψ :: Γ =>
    have : 𝔇 (⋀(ψ :: Γ) :: Δ) := conj₂ (Γ := ψ :: Γ) (fun χ h ↦ d χ (by simp_all))
    and (d φ (by simp)) this

open Entailment

/-- An entailment relation which is determined solely by derivability. -/
class PrincipalEntailment (𝔇 : outParam (List F → Type*)) {P : Type*} [Entailment P F] (𝓟 : P) where
  equiv {φ} : 𝓟 ⊢! φ ≃ 𝔇 [φ]

namespace PrincipalEntailment

variable {P : Type*} [Entailment P F] {𝓟 : P} [PrincipalEntailment 𝔇 𝓟]

omit [LogicalConnective F] [LogicalNeutral F]
  [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] in
lemma provable_iff :
    𝓟 ⊢ φ ↔ Nonempty (𝔇 [φ]) := by
  simpa using! OneSidedLK.PrincipalEntailment.equiv.nonempty_congr

variable [OneSidedLK.Cut 𝔇] (𝓟)

instance : Entailment.ModusPonens 𝓟 where
  mdp {φ ψ} b₁ b₂ :=
    let b₁ := equiv b₁
    let b₂ := equiv b₂
    have : 𝔇 [∼(φ 🡒 ψ), ∼φ, ψ] := cast (tensor (𝔇 := 𝔇) (identity φ) (identity (∼ψ))) (by simp [LogicalConnective.DeMorgan.imply])
    have : 𝔇 [∼φ, ψ] := contraction (cut b₁ this) (by simp)
    have : 𝔇 [ψ] := contraction (cut b₂ this) (by simp)
    equiv.symm <| cast this

instance : Entailment.Cl 𝓟 where
  negEquiv {φ} := Entailment.cast
    (show 𝓟 ⊢! (φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ) from
      equiv.symm <| and (or <| swap₁ <| or <| close φ) (or <| and (identity φ) top))
    (by simp [Axioms.NegEquiv, LogicalConnective.DeMorgan.imply, LogicalConnective.iff])
  verum := equiv.symm <| verum
  implyK {φ ψ} :=
    have : 𝓟 ⊢! ∼φ ⋎ ∼ψ ⋎ φ := equiv.symm <| or <| swap₁ <| or <| close φ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  implyS {φ ψ χ} :=
    have : 𝓟 ⊢! φ ⋏ ψ ⋏ ∼χ ⋎ φ ⋏ ∼ψ ⋎ ∼φ ⋎ χ :=
      equiv.symm <| or <| swap₁ <| or <| swap₁ <| or <| swap₃ <| and
        (close φ)
        (and (swap₃ <| and (close φ) (close ψ)) (close χ))
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  and₁ {φ ψ} :=
    have : 𝓟 ⊢! (∼φ ⋎ ∼ψ) ⋎ φ :=  equiv.symm <|or <| or <| close φ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  and₂ {φ ψ} :=
    have : 𝓟 ⊢! (∼φ ⋎ ∼ψ) ⋎ ψ := equiv.symm <| or <| or <| close ψ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  and₃ {φ ψ} :=
    have : 𝓟 ⊢! ∼φ ⋎ ∼ψ ⋎ φ ⋏ ψ := equiv.symm <| or <| swap₁ <| or <| swap₁ <| and (close φ) (close ψ)
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  or₁ {φ ψ} :=
    have : 𝓟 ⊢! ∼φ ⋎ φ ⋎ ψ := equiv.symm <| or <| swap₁ <| or <| close φ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  or₂ {φ ψ} :=
    have : 𝓟 ⊢! ∼ψ ⋎ φ ⋎ ψ := equiv.symm <| or <| swap₁ <| or <| close ψ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  or₃ {φ ψ χ} :=
    have : 𝓟 ⊢! φ ⋏ ∼χ ⋎ ψ ⋏ ∼ χ ⋎ ∼φ ⋏ ∼ψ ⋎ χ :=
      equiv.symm <| or <| swap₁ <| or <| swap₁ <| or <| and
        (swap₃ <| and (close φ) (close χ))
        (swap₂ <| and (close ψ) (close χ))
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  dne {φ} :=
    have : 𝓟 ⊢! ∼φ ⋎ φ := equiv.symm <| or <| close φ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])

variable {𝓟}

end PrincipalEntailment

abbrev Pullback (𝔇 : List F → Type*) {G : Type*} [LogicalConnective G] [LogicalNeutral G] (f : G →ˡᶜ F) : List G → Type _ := fun Γ ↦ 𝔇 (Γ.map f)

namespace Pullback

variable {G : Type*} [LogicalConnective G] [LogicalNeutral G]
  [TildeInvolutive G] [LogicalConnective.DeMorgan G] [LogicalNeutral.DeMorgan G] {f : G →ˡᶜ F}

def cast (d : 𝔇 Δ) (h : Δ = Γ.map f := by simp) : Pullback 𝔇 f Γ := by
  unfold Pullback
  exact h ▸ d

def uncast (d : Pullback 𝔇 f Γ) (h : Δ = Γ.map f := by simp) : 𝔇 Δ := h ▸ d

instance oneSidedLK [OneSidedLK 𝔇] : OneSidedLK (Pullback 𝔇 f) where
  identity φ := cast <| identity (f φ)
  contraction {Δ Γ} d h := cast (contraction d (List.map_subset f h) : 𝔇 (Γ.map f)) (by simp)
  verum := cast verum
  and d₁ d₂ := cast <| and d₁ d₂
  or d := cast <| or d

instance cut [Cut 𝔇] : Cut (Pullback 𝔇 f) where
  cut {φ Γ Δ} bp bn :=
    have bp : 𝔇 (f φ :: Γ.map f) := uncast bp
    have bn : 𝔇 (∼f φ :: Δ.map f) := uncast bn
    cast (Cut.cut bp bn)

instance {P : Type*} [Entailment P F] (𝓟 : P) [PrincipalEntailment 𝔇 𝓟] :
    PrincipalEntailment (Pullback 𝔇 f) (Entailment.pullback 𝓟 f) where
  equiv {φ} := PrincipalEntailment.equiv (φ := f φ)

omit [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F]
  [TildeInvolutive G] [LogicalConnective.DeMorgan G] [LogicalNeutral.DeMorgan G] in
@[simp] lemma nonempty_iff {Γ} : Nonempty (Pullback 𝔇 f Γ) ↔ Nonempty (𝔇 (Γ.map f)) := by simp [Pullback]

end Pullback

/-- An entailment relation which is determined by a context and derivability. -/
class ContextualEntailment (𝔇 : outParam (List F → Type*)) (S : Type*) [Entailment S F] [AdjunctiveSet F S] where
  equiv {𝓢 : S} {φ} : 𝓢 ⊢! φ ≃ (l : {l : List F // ∀ φ ∈ l, φ ∈ 𝓢}) × 𝔇 (φ :: ∼l)

namespace ContextualEntailment

variable {S : Type*} [Entailment S F] [AdjunctiveSet F S] [ContextualEntailment 𝔇 S]

omit [LogicalNeutral F] [TildeInvolutive F] [LogicalConnective.DeMorgan F] [LogicalNeutral.DeMorgan F] in
lemma provable_iff {𝓢 : S} :
    𝓢 ⊢ φ ↔ ∃ Γ : List F, (∀ ψ ∈ Γ, ψ ∈ 𝓢) ∧ Nonempty (𝔇 (φ :: ∼Γ)) := by
  simpa using! equiv.nonempty_congr

def toProof (𝓢 : S) (d : 𝔇 [φ]) : 𝓢 ⊢! φ := equiv.symm ⟨⟨[], by simp⟩, d⟩

def ofAxiom [OneSidedLK 𝔇] {𝓢 : S} (h : φ ∈ 𝓢) : 𝓢 ⊢! φ :=
  equiv.symm ⟨⟨[φ], by simp_all⟩, identity φ⟩

def ofAxiomSubset {𝓢 𝓤 : S} : 𝓢 ⊢! φ → 𝓢 ⊆ 𝓤 → 𝓤 ⊢! φ := fun b h ↦
  have ⟨l, d⟩ := equiv b
  equiv.symm
    ⟨⟨l, fun φ hφ ↦ AdjunctiveSet.subset_iff.mp h _ (l.prop φ hφ)⟩, d⟩

instance [OneSidedLK 𝔇] : Entailment.Axiomatized S where
  prfAxm h := ofAxiom h
  weakening h d := ofAxiomSubset d h

variable [OneSidedLK.Cut 𝔇]

instance (𝓢 : S) : Entailment.ModusPonens 𝓢 where
  mdp {φ ψ} b₁ b₂ :=
    let ⟨Γ₁, b₁⟩ := equiv b₁
    let ⟨Γ₂, b₂⟩ := equiv b₂
    have : 𝔇 [∼(φ 🡒 ψ), ∼φ, ψ] := cast (tensor (𝔇 := 𝔇) (identity φ) (identity (∼ψ))) (by simp [LogicalConnective.DeMorgan.imply])
    have : 𝔇 (∼φ :: ψ :: ∼↑Γ₁) := contraction (cut b₁ this) (by simp)
    have : 𝔇 (ψ :: ∼↑Γ₁ ++ ∼↑Γ₂) := contraction (cut b₂ this) (by simp)
    equiv.symm ⟨⟨Γ₁ ++ Γ₂, by simp; grind⟩, cast this⟩

instance : Entailment.DeductiveExplosion S where
  dexp b φ :=
    have ⟨Γ, b⟩ := equiv b
    equiv.symm
    ⟨ Γ,
      have : 𝔇 [∼⊥] := cast verum (by simp)
      contraction (cut b this) (by simp) ⟩

instance cl (𝓢 : S) : Entailment.Cl 𝓢 where
  negEquiv {φ} := Entailment.cast
    (show 𝓢 ⊢! (φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ) from
      toProof _ <| and (or <| swap₁ <| or <| close φ) (or <| and (identity φ) top))
    (by simp [Axioms.NegEquiv, LogicalConnective.DeMorgan.imply, LogicalConnective.iff])
  verum := toProof _ <| verum
  implyK {φ ψ} :=
    have : 𝓢 ⊢! ∼φ ⋎ ∼ψ ⋎ φ := toProof _ <| or <| swap₁ <| or <| close φ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  implyS {φ ψ χ} :=
    have : 𝓢 ⊢! φ ⋏ ψ ⋏ ∼χ ⋎ φ ⋏ ∼ψ ⋎ ∼φ ⋎ χ :=
      toProof _ <| or <| swap₁ <| or <| swap₁ <| or <| swap₃ <| and
        (close φ)
        (and (swap₃ <| and (close φ) (close ψ)) (close χ))
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  and₁ {φ ψ} :=
    have : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ⋎ φ :=  toProof _ <|or <| or <| close φ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  and₂ {φ ψ} :=
    have : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ⋎ ψ := toProof _ <| or <| or <| close ψ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  and₃ {φ ψ} :=
    have : 𝓢 ⊢! ∼φ ⋎ ∼ψ ⋎ φ ⋏ ψ := toProof _ <| or <| swap₁ <| or <| swap₁ <| and (close φ) (close ψ)
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  or₁ {φ ψ} :=
    have : 𝓢 ⊢! ∼φ ⋎ φ ⋎ ψ := toProof _ <| or <| swap₁ <| or <| close φ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  or₂ {φ ψ} :=
    have : 𝓢 ⊢! ∼ψ ⋎ φ ⋎ ψ := toProof _ <| or <| swap₁ <| or <| close ψ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  or₃ {φ ψ χ} :=
    have : 𝓢 ⊢! φ ⋏ ∼χ ⋎ ψ ⋏ ∼ χ ⋎ ∼φ ⋏ ∼ψ ⋎ χ :=
      toProof _ <| or <| swap₁ <| or <| swap₁ <| or <| and
        (swap₃ <| and (close φ) (close χ))
        (swap₂ <| and (close ψ) (close χ))
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])
  dne {φ} :=
    have : 𝓢 ⊢! ∼φ ⋎ φ := toProof _ <| or <| close φ
    Entailment.cast this (by simp [LogicalConnective.DeMorgan.imply])

end ContextualEntailment
end OneSidedLK
end LO
end

/- GID: D5/S3/ConceptDynamics/ZfcLogic/LogicSymbolOne
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcLogic/LogicSymbolOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logic.LogicSymbol for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcFiniteCollections.List
public import D5.S3.ConceptDynamics.ZfcLanguageSupport.NotationClass

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Logic/LogicSymbol.lean, original lines 1-319.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO

/--
A class for types with logical connectives $\top, \bot, \land, \lor, \to, \lnot$.
-/
class LogicalConnective (α : Type*) extends Tilde α, Arrow α, Wedge α, Vee α

class LogicalNeutral (α : Type*) extends Top α, Bot α

class TildeInvolutive (F : Type*) [Tilde F] where
  tilde_involutive (φ : F) : ∼∼φ = φ

class LogicalConnective.DeMorgan (F : Type*) [LogicalConnective F] where
  imply (φ ψ : F) : φ 🡒 ψ = ∼φ ⋎ ψ
  and (φ ψ : F) : ∼(φ ⋏ ψ) = ∼φ ⋎ ∼ψ
  or (φ ψ : F) : ∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ

class LogicalNeutral.DeMorgan (F : Type*) [LogicalNeutral F] [Tilde F] where
  verum : ∼(⊤ : F) = ⊥
  falsum : ∼(⊥ : F) = ⊤

attribute [simp, grind =] TildeInvolutive.tilde_involutive
attribute [simp, grind =] LogicalNeutral.DeMorgan.verum LogicalNeutral.DeMorgan.falsum LogicalConnective.DeMorgan.and LogicalConnective.DeMorgan.or

section tilde

variable {α : Type*} [Tilde α] [TildeInvolutive α]

@[simp] lemma TildeInvolutive.tilde_injective : Function.Injective (∼· : α → α) := by
  intro φ ψ h
  simpa using congr_arg (∼·) h

@[simp] lemma TildeInvolutive.tilde_eq_tilde_iff_eq {φ ψ : α} : ∼φ = ∼ψ ↔ φ = ψ :=
  Function.Injective.eq_iff TildeInvolutive.tilde_injective

end tilde

namespace LogicalConnective

section
variable {α : Type*} [LogicalConnective α]

@[match_pattern] def iff (a b : α) := (a 🡒 b) ⋏ (b 🡒 a)

/--
A defined logical connective for "iff", defined from the logical connectives `🡒` and `⋏`.
-/
infix:61 " 🡘 " => LogicalConnective.iff

end

@[reducible]
instance PropLogicSymbols : LogicalConnective Prop where
  arrow := fun P Q => (P → Q)
  wedge := And
  vee := Or
  tilde := Not

instance PropLogicalNeutral : LogicalNeutral Prop where
  top := True
  bot := False

@[simp] lemma Prop.neg_eq (φ : Prop) : ∼φ = ¬φ := rfl

@[simp] lemma Prop.arrow_eq (φ ψ : Prop) : (φ 🡒 ψ) = (φ → ψ) := rfl

@[simp] lemma Prop.and_eq (φ ψ : Prop) : (φ ⋏ ψ) = (φ ∧ ψ) := rfl

@[simp] lemma Prop.or_eq (φ ψ : Prop) : (φ ⋎ ψ) = (φ ∨ ψ) := rfl

@[simp] lemma Prop.iff_eq (φ ψ : Prop) : (φ 🡘 ψ) = (φ ↔ ψ) := by simp [LogicalConnective.iff, iff_iff_implies_and_implies]

/--
A class for a type `F` which contains homomorphisms (for logical connectives) from `α` to `β`.
-/
class HomClass (F : Type*) (α β : outParam Type*)
    [LogicalConnective α] [LogicalNeutral α] [LogicalConnective β] [LogicalNeutral β] [FunLike F α β] where
  map_top : ∀ (f : F), f ⊤ = ⊤
  map_bot : ∀ (f : F), f ⊥ = ⊥
  map_neg : ∀ (f : F) (φ : α), f (∼φ) = ∼f φ
  map_imply : ∀ (f : F) (φ ψ : α), f (φ 🡒 ψ) = f φ 🡒 f ψ
  map_and : ∀ (f : F) (φ ψ : α), f (φ ⋏ ψ) = f φ ⋏ f ψ
  map_or  : ∀ (f : F) (φ ψ : α), f (φ ⋎ ψ) = f φ ⋎ f ψ

attribute [simp, grind =] HomClass.map_top HomClass.map_bot HomClass.map_neg HomClass.map_imply HomClass.map_and HomClass.map_or

namespace HomClass

variable (F : Type*) (α β : outParam Type*) [LogicalConnective α] [LogicalNeutral α] [LogicalConnective β] [LogicalNeutral β] [FunLike F α β]
variable [HomClass F α β]
variable (f : F) (a b : α)

@[simp] lemma map_iff : f (a 🡘 b) = f a 🡘 f b := by simp [LogicalConnective.iff]

end HomClass

variable (α β γ : Type*)
  [LogicalConnective α] [LogicalConnective β] [LogicalConnective γ]
  [LogicalNeutral α] [LogicalNeutral β] [LogicalNeutral γ]

structure Hom where
  toTr : α → β
  map_top' : toTr ⊤ = ⊤
  map_bot' : toTr ⊥ = ⊥
  map_neg' : ∀ φ, toTr (∼φ) = ∼toTr φ
  map_imply' : ∀ φ ψ, toTr (φ 🡒 ψ) = toTr φ 🡒 toTr ψ
  map_and' : ∀ φ ψ, toTr (φ ⋏ ψ) = toTr φ ⋏ toTr ψ
  map_or'  : ∀ φ ψ, toTr (φ ⋎ ψ) = toTr φ ⋎ toTr ψ

/--
A structure for homomorphisms (for logical connectives) from `α` to `β`.
-/
infix:25 " →ˡᶜ " => Hom

namespace Hom
variable {α β γ}

instance : FunLike (α →ˡᶜ β) α β where
  coe := toTr
  coe_injective := by
    intro f g h; rcases f; rcases g; simpa using h

instance : HomClass (α →ˡᶜ β) α β where
  map_top := map_top'
  map_bot := map_bot'
  map_neg := map_neg'
  map_imply := map_imply'
  map_and := map_and'
  map_or := map_or'

variable (f : α →ˡᶜ β) (a b : α)

end Hom

-- `AndOrClosed.verum`/`AndOrClosed.falsum` have `C` (a variable) as the simp LHS head symbol,
-- since `C` is the predicate being closed under `⊤`/`⊥`. They are intentionally kept as global
-- simp lemmas (`⊤`/`⊥` are always in any `AndOrClosed` predicate); scoping them would break
-- implicit uses elsewhere.

end LogicalConnective

/-
section Subclosed

class Tilde.Subclosed [Tilde F] (C : F → Prop) where
  tilde_closed : C (∼φ) → C φ

class Arrow.Subclosed [Arrow F] (C : F → Prop) where
  arrow_closed : C (φ 🡒 ψ) → C φ ∧ C ψ

class Wedge.Subclosed [Wedge F] (C : F → Prop) where
  wedge_closed : C (φ ⋏ ψ) → C φ ∧ C ψ

class Vee.Subclosed [Vee F] (C : F → Prop) where
  vee_closed : C (φ ⋎ ψ) → C φ ∧ C ψ

attribute [aesop safe 5 forward]
  Tilde.Subclosed.tilde_closed
  Arrow.Subclosed.arrow_closed
  Wedge.Subclosed.wedge_closed
  Vee.Subclosed.vee_closed

class LogicalConnective.Subclosed [LogicalConnective F] (C : F → Prop) extends
  Tilde.Subclosed C,
  Arrow.Subclosed C,
  Wedge.Subclosed C,
  Vee.Subclosed C

end Subclosed
-/

section conjdisj

variable {α β : Type*}
  [LogicalConnective α] [LogicalConnective β]
  [LogicalNeutral α] [LogicalNeutral β]

end conjdisj

end LO

end

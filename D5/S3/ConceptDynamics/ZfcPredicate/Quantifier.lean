/- GID: D5/S3/ConceptDynamics/ZfcPredicate/Quantifier
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcPredicate/Quantifier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Syntax.Predicate.Quantifier for first-order set definition elimination. -/
module

public import D5.S3.ConceptDynamics.ZfcFiniteCollections.List
public import D5.S3.ConceptDynamics.ZfcLanguageSupport.NotationClass
public import D5.S3.ConceptDynamics.ZfcLogic.LogicSymbolTwo

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Syntax/Predicate/Quantifier.lean, original lines 1-296.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO

namespace Polarity

section symbol

end symbol

end Polarity

namespace SigmaPiDelta

end SigmaPiDelta

namespace FirstOrder

class UnivQuantifier (α : ℕ → Type*) where
  all : α (n + 1) → α n

prefix:64 "∀¹ " => UnivQuantifier.all

class ExsQuantifier (α : ℕ → Type*) where
  exs : α (n + 1) → α n

prefix:64 "∃¹ " => ExsQuantifier.exs

attribute [match_pattern] UnivQuantifier.all ExsQuantifier.exs

class Quantifier (α : ℕ → Type*) extends UnivQuantifier α, ExsQuantifier α

/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → Type*) extends Quantifier α where
  connectives : (n : ℕ) → LogicalConnective (α n)
  neutrals : (n : ℕ) → LogicalNeutral (α n)

instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalConnective (α n) := LCWQ.connectives n

instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalNeutral (α n) := LCWQ.neutrals n

instance (α : ℕ → Type*) [Quantifier α] [(n : ℕ) → LogicalConnective (α n)]
    [(n : ℕ) → LogicalNeutral (α n)] : LCWQ α where
  connectives := inferInstance
  neutrals := inferInstance

section UnivQuantifier

variable {α : ℕ → Type*} [UnivQuantifier α]

def allClosure : {n : ℕ} → α n → α 0
  |     0, a => a
  | _ + 1, a => allClosure (∀¹ a)

/--
The universal closure of a formula.
-/
prefix:64 "∀¹* " => allClosure

@[simp] lemma allClosure_zero (a : α 0) : ∀¹* a = a := rfl

lemma allClosure_succ {n} (a : α (n + 1)) : ∀¹* a = ∀¹* ∀¹ a := rfl

def allItr : (k : ℕ) → α (n + k) → α n
  |     0, a => a
  | k + 1, a => allItr k (∀¹ a)

notation "∀¹^[" k "] " φ:64 => allItr k φ

@[simp] lemma allItr_zero (a : α n) : ∀¹^[0] a = a := rfl

lemma allItr_succ {k} (a : α (n + (k + 1))) : ∀¹^[k + 1] a = ∀¹^[k] (∀¹ a) := rfl

end UnivQuantifier

section ExsQuantifier

variable {α : ℕ → Type*} [ExsQuantifier α]

def exsClosure : {n : ℕ} → α n → α 0
  |     0, a => a
  | _ + 1, a => exsClosure (∃¹ a)

/--
The existential closure of a formula.
-/
prefix:64 "∃¹* " => exsClosure

end ExsQuantifier

section quantifier

variable {α : ℕ → Type*}

def ball [UnivQuantifier α] [Arrow (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∀¹ (φ 🡒 ψ)

def bexs [ExsQuantifier α] [Wedge (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n := ∃¹ (φ ⋏ ψ)

/-- A bounded universal quantifier. `∀¹[φ] ψ` is defined as `∀¹ (φ 🡒 ψ)`. -/
notation:64 "∀¹[" φ "] " ψ => ball φ ψ

/-- A bounded existential quantifier. `∃¹[φ] ψ` is defined as `∃¹ (φ ⋏ ψ)`. -/
notation:64 "∃¹[" φ "] " ψ => bexs φ ψ

end quantifier

end FirstOrder

namespace SecondOrder

section UnivQuantifier

end UnivQuantifier

section ExsQuantifier

end ExsQuantifier

section quantifier

variable {α : ℕ → ℕ → Type*}

end quantifier

end SecondOrder

end LO

end

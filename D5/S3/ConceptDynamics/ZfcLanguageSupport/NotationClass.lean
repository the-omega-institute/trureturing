/- GID: D5/S3/ConceptDynamics/ZfcLanguageSupport/NotationClass
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ZfcLanguageSupport/NotationClass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic.TypeStar]
   utility: none
   digest: Vorspiel.NotationClass for first-order set definition elimination. -/
module

public import Mathlib.Tactic.TypeStar
public import Mathlib.Data.Nat.Basic

/- Source: FormalizedFormalLogic/Foundation@30a16ffa93d79d73ab4d02427fa00f50e039bf29
   Foundation/Vorspiel/NotationClass.lean, original lines 1-136.
   Modifications: source-command excerpt; canonical header, reduced imports, and capacity scopes.
   Retained proofs and required notices preserve attribution. Apache-2.0 license:
   Library/ConceptDynamics/foundation2026firstorder.md.
   Retirement: direct Mathlib reference when the repository pin supplies a
   proved-equivalent interface and its faithful bridge elaborates. -/

@[expose] public section

namespace LO

class HTilde (α : Type*) (β : outParam Type*) where
  hTilde : α → β

prefix:75 "∼" => HTilde.hTilde
macro_rules | `(∼$x) => `(unop% HTilde.hTilde $x)

class HArrow (α β : Type*) (γ : outParam Type*) where
  hArrow : α → β → γ

infixr:60 " 🡒 " => HArrow.hArrow
macro_rules | `($x 🡒 $y) => `(binop% HArrow.hArrow $x $y)

class HWedge (α β : Type*) (γ : outParam Type*) where
  hWedge : α → β → γ

infixr:69 " ⋏ " => HWedge.hWedge
macro_rules | `($x ⋏ $y) => `(binop% HWedge.hWedge $x $y)

class HVee (α β : Type*) (γ : outParam Type*) where
  hVee : α → β → γ

infixr:68 " ⋎ " => HVee.hVee
macro_rules | `($x ⋎ $y) => `(binop% HVee.hVee $x $y)

attribute [match_pattern]
  HTilde.hTilde
  HArrow.hArrow
  HWedge.hWedge
  HVee.hVee

class Tilde (α : Type*) where
  tilde : α → α

class Arrow (α : Type*) where
  arrow : α → α → α

class Wedge (α : Type*) where
  wedge : α → α → α

class Vee (α : Type*) where
  vee : α → α → α

attribute [match_pattern]
  Tilde.tilde
  Arrow.arrow
  Wedge.wedge
  Vee.vee

@[default_instance]
instance Tilde.instHTilde [Tilde α] : HTilde α α := ⟨Tilde.tilde⟩

@[default_instance]
instance Arrow.instHArrow [Arrow α] : HArrow α α α := ⟨Arrow.arrow⟩

@[default_instance]
instance Wedge.instHWedge [Wedge α] : HWedge α α α := ⟨Wedge.wedge⟩

@[default_instance]
instance Vee.instHVee [Vee α] : HVee α α α := ⟨Vee.vee⟩

class Length (α : Type*) where
  length : α → α

notation "‖" x "‖" => Length.length x

/-- Coding objects into syntactic objects (e.g. natural numbers, first-order terms) -/
class GödelQuote (α β : Sort*) where
  quote : α → β

notation:max "⌜" x "⌝" => GödelQuote.quote x

end LO

end

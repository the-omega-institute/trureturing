module
import all Init.Meta.Defs
public import OmegaChecks.InitPort.Alternatives.NameText

/-! Equality of a hierarchical name compares its component and its parent. -/

open Lean
namespace OmegaChecks.InitPort.Alternatives

private theorem bothTrue (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

private theorem nodeEquality {α : Type} [BEq α] [law : LawfulBEq α]
    (node : Name → α → Name) {p q : Name} {a b : α}
    (parent : p.beq q = true ↔ p = q)
    (inj : node p a = node q b → p = q ∧ a = b) :
    ((a == b) && p.beq q) = true ↔ node p a = node q b := by
  constructor
  · intro h
    obtain ⟨label, parentEq⟩ := (bothTrue _ _).mp h
    cases parent.mp parentEq
    cases law.eq_of_beq label
    rfl
  · intro h
    obtain ⟨parentEq, label⟩ := inj h
    cases label
    exact (bothTrue _ _).mpr ⟨law.rfl, parent.mpr parentEq⟩

public theorem Lean.Name.beq_iff_eq : type_of% @_root_.Lean.Name.beq_iff_eq := by
  intro m n
  induction m generalizing n <;> cases n
  case str.str p s ih q t => exact nodeEquality Name.str (ih (n := q)) Name.str.inj
  case num.num p k ih q l => exact nodeEquality Name.num (ih (n := q)) Name.num.inj
  case anonymous.anonymous => exact ⟨fun _ => rfl, fun _ => rfl⟩
  all_goals constructor <;> intro h <;> cases h

@[instance_reducible] public def Lean.Name.instDecidableEq : type_of% @_root_.Lean.Name.instDecidableEq :=
  fun a b => if h : a == b then
    isTrue (Lean.Name.beq_iff_eq.mp h)
  else
    isFalse fun equal => h (Lean.Name.beq_iff_eq.mpr equal)

end OmegaChecks.InitPort.Alternatives

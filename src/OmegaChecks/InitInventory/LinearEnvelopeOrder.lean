module
public import OmegaChecks.InitInventory.EnvelopeOrder
import all Init.Grind.Module.Envelope
import Init.GrindInstances.Ring.Nat

public section
namespace OmegaChecks.InitBoundaries.LinearEnvelopeOrder
open Lean.Grind Std
universe u

private def tag (p q : Prop) : Nat → Prop
  | 0 => p
  | _+1 => q

/-- Every ordinary natural inequality is admitted. For a descending pair,
adding one can exchange two equivalent propositions. -/
private def comparison (p q : Prop) (a b : Nat) : Prop :=
  if a ≤ b then True else tag p q b

private theorem normal {p q : Prop} (h : p ↔ q) (a b : Nat) :
    comparison p q a b ↔ (a ≤ b ∨ p) := by
  unfold comparison
  split
  next hab => exact ⟨fun _ => .inl hab, fun _ => True.intro⟩
  next hn =>
    have w : tag p q b ↔ p := by cases b <;> first | exact Iff.rfl | exact h.symm
    exact ⟨fun hp => .inr (w.mp hp), fun hw => w.mpr (hw.resolve_left hn)⟩

@[instance_reducible] private def order (p q : Prop) : LE Nat := ⟨comparison p q⟩

private theorem linear {p q : Prop} (h : p ↔ q) : @IsLinearPreorder Nat (order p q) :=
  @IsLinearPreorder.mk Nat (order p q)
    (@IsPreorder.mk Nat (order p q)
      (fun a => (normal h a a).mpr (.inl (Nat.le_refl a)))
      (fun a b c hab hbc => (normal h a c).mpr (Or.elim ((normal h a b).mp hab)
        (fun ab => Or.elim ((normal h b c).mp hbc) (fun bc => .inl (Nat.le_trans ab bc)) Or.inr) Or.inr)))
    (fun a b => (Nat.le_total a b).elim
      (fun ab => .inl ((normal h a b).mpr (.inl ab)))
      (fun ba => .inr ((normal h b a).mpr (.inl ba))))

private theorem ordered {p q : Prop} (h : p ↔ q) :
    @OrderedAdd Nat _ (order p q) (linear h).toIsPreorder :=
  @OrderedAdd.mk Nat _ (order p q) (linear h).toIsPreorder (fun {a b} c =>
    (normal h a b).trans ((or_congr (Iff.intro (fun h => Nat.add_le_add_right h c)
      (fun h => Nat.le_of_add_le_add_right h)) Iff.rfl).trans (normal h (a+c) (b+c)).symm))

/-- Representative coherence with exactly the stronger order assumption in instIsLinearPreorderQ. -/
abbrev LinearCoherence := ∀ {α : Type u} [m : NatModule α] [le : LE α] [lin : IsLinearPreorder α]
    [ord : OrderedAdd α], type_of% (@IntModule.OfNatModule.instLEQOfOrderedAdd._proof_3 α m le lin.toIsPreorder ord)

theorem propextFromLinearLift (respect : LinearCoherence.{0}) : type_of% @propext := by
  intro p q h
  exact @respect Nat inferInstance (order p q) (linear h) (ordered h)
    (1,0) (0,0) (2,1) (0,0) ⟨0, rfl⟩ ⟨0, rfl⟩

theorem linearLiftFromPropext (ext : type_of% @propext) : LinearCoherence.{u} :=
  fun {_} _ _ _ _ => EnvelopeOrder.moduleLiftFromPropext ext

end OmegaChecks.InitBoundaries.LinearEnvelopeOrder

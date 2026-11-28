module
public import Init.Data.Fin.Lemmas
public meta import Lean

/-! The value functions compared by zero left addition at each finite bound. -/

public section
namespace OmegaChecks.InitBoundaries.FinAddition

def BoundedZeroAddition : Prop :=
  ∀ n : Nat, (fun i : Fin n => 0 + i.val) = (fun i => i.val)

private theorem pack {α : Type u} {n : Nat} {f g : α → Nat} (h : f = g)
    (hf : ∀ x, f x < n) (hg : ∀ x, g x < n) :
    (fun x => (⟨f x, hf x⟩ : Fin n)) = (fun x => ⟨g x, hg x⟩) := by
  cases h
  rfl

theorem equivalence : (type_of% @Fin.natAdd_zero) ↔ BoundedZeroAddition := by
  constructor
  · intro rule n
    exact congrArg (fun f : Fin n → Fin (0 + n) => fun i => (f i).val) (@rule n)
  · intro law n
    exact pack (law n) (fun i => (Fin.natAdd 0 i).isLt)
      (fun i => (Fin.cast (Nat.zero_add n).symm i).isLt)

theorem ofZeroAddition (h : (fun x : Nat => 0 + x) = (fun x => x)) : BoundedZeroAddition :=
  fun n => congrArg (fun f : Nat → Nat => fun i : Fin n => f i.val) h

theorem pointwise {n : Nat} (i : Fin n) : Fin.natAdd 0 i = Fin.cast (Nat.zero_add n).symm i :=
  Fin.ext (Nat.zero_add i.val)

end OmegaChecks.InitBoundaries.FinAddition

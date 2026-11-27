module
public import Init.Core

namespace OmegaChecks.InitPort.Alternatives

/-- Lift the value together with its fiber type. Heterogeneous equality makes these pairs equal. -/
private def quotientHRec {α : Sort u} {r : α → α → Prop} {motive : Quot r → Sort v}
    (q : Quot r) (f : (a : α) → motive (Quot.mk r a))
    (c : (a b : α) → r a b → HEq (f a) (f b)) : motive q :=
  have packHEq {A B : Sort v} {a : A} {b : B} (e : HEq a b) :
      (⟨A, a⟩ : (T : Sort v) ×' T) = ⟨B, b⟩ := by
    cases e
    rfl
  let packed := Quot.lift (fun a => (⟨motive (Quot.mk r a), f a⟩ : (T : Sort v) ×' T))
    (fun a b rel => packHEq (c a b rel))
  have fiber (x : Quot r) : (packed x).1 = motive x :=
    Quot.ind (β := fun x => (packed x).1 = motive x) (fun _ => rfl) x
  cast (fiber q) (packed q).2

public def Quot.hrecOn : type_of% @_root_.Quot.hrecOn := @quotientHRec

end OmegaChecks.InitPort.Alternatives

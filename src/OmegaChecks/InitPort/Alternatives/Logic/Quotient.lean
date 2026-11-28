module
public import Init.Core

/-!
The native quotient supplies induction into propositions and a nondependent lift.
For `Quot.rec`, `Quot.recOn` and the two `Quotient` versions, even the official
coherence premise uses quotient soundness to transport between fibers.

The original types of `Quot.recOnSubsingleton`, `Quotient.recOnSubsingleton`,
`Quotient.recOnSubsingleton₂` and both `pliftOn` operations admit direct terms in
the representative model: the quotient point itself supplies a representative.
That operation is unavailable on the native carrier. These five interfaces remain open
there. In `InitInventory.Quotient`, `QuotientFibers` builds each unary subsingleton
recursor from the corresponding `pliftOn`. The setoid binary recursor can be built
from unary recursors at the two carrier universes. At equal carrier universes a
binary recursor also gives back a unary one. For `Quotient.exact`, decidability of the setoid relation suffices by
`QuotientDecision.exactOfDecidable` in `OmegaChecks.InitInventory.Quotient`.
The official type quantifies over arbitrary setoids.
-/

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

public theorem Quotient.recOnSubsingleton₂._proof_1 :
    type_of% @_root_.Quotient.recOnSubsingleton₂._proof_1 := by
  intro α β s₁ s₂ motive fibers q a
  exact _root_.Quotient.ind (motive := fun b => Subsingleton (motive (Quotient.mk s₁ a) b))
    (fibers a) q

end OmegaChecks.InitPort.Alternatives

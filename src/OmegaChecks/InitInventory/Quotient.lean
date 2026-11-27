module
public import OmegaChecks.InitPort.Alternatives.Logic.Quotient
import all OmegaChecks.InitPort.Alternatives.Logic.Quotient

/-! The two public heterogeneous quotient eliminators have constructively inhabited types.
The pinned abbreviations reduce through a pair whose first component is the quotient
point. Equality of those pairs entails quotient soundness even for the unit motive. -/

namespace OmegaChecks.InitBoundaries.HeterogeneousQuotient

public abbrev hrecOn : type_of% @_root_.Quot.hrecOn :=
  @OmegaChecks.InitPort.Alternatives.Quot.hrecOn

public def hrecOnSetoid : type_of% @_root_.Quotient.hrecOn :=
  fun {α} {s} {motive} q f c => @hrecOn α s.r motive q f c

public theorem agrees.{u,v} {α : Sort u} {r : α → α → Prop} {motive : Quot r → Sort v}
    (q : Quot r) (f : (a : α) → motive (Quot.mk r a))
    (c : (a b : α) → r a b → HEq (f a) (f b)) :
    hrecOn q f c = _root_.Quot.hrecOn q f c := by
  induction q using Quot.ind
  rfl

public theorem setoidAgrees {α : Sort u} {s : Setoid α} {motive : Quotient s → Sort v}
    (q : Quotient s) (f : (a : α) → motive (Quotient.mk s a))
    (c : (a b : α) → s.r a b → HEq (f a) (f b)) :
    hrecOnSetoid q f c = _root_.Quotient.hrecOn q f c := agrees q f c

public theorem soundOfPairCoherence
    (coherent : ∀ {α : Sort u} {r : α → α → Prop} (a b : α), r a b →
      Quot.indep (motive := fun _ : Quot r => Unit) (fun _ => ()) a =
        Quot.indep (motive := fun _ : Quot r => Unit) (fun _ => ()) b) :
    type_of% @_root_.Quot.sound.{u} :=
  fun {α r a b} related => congrArg PSigma.fst (@coherent α r a b related)

public theorem setoidSoundOfPairCoherence
    (coherent : ∀ {α : Sort u} {s : Setoid α} (a b : α), s.r a b →
      Quot.indep (motive := fun _ : Quotient s => Unit) (fun _ => ()) a =
        Quot.indep (motive := fun _ : Quotient s => Unit) (fun _ => ()) b) :
    type_of% @_root_.Quotient.sound.{u} :=
  fun {α s a b} related => congrArg PSigma.fst (@coherent α s a b related)

end OmegaChecks.InitBoundaries.HeterogeneousQuotient

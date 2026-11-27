module

public import OmegaChecks.InitPort.Alternatives.NatFold
public import OmegaChecks.InitPort.Alternatives.Fin
import all OmegaChecks.InitPort.Alternatives.Fin
import all OmegaChecks.InitPort.Alternatives.NatFold
import all Init.Data.Nat.Basic

namespace OmegaChecks.Interface.Equations

public theorem Fin.natAdd {m : Nat} (n : Nat) (i : Fin m) :
    OmegaChecks.InitPort.Alternatives.Fin.natAdd n i = _root_.Fin.natAdd n i := by
  cases n with
  | zero => exact Fin.ext (Nat.zero_add i.val).symm
  | succ => rfl

public theorem Fin.foldlTR {α : Sort u} (n : Nat) (f : α → Fin n → α) (init : α) :
    _root_.Fin.foldl n f init = _root_.Fin.foldlTR n f init :=
  congrArg (fun k => @k α n f init) _root_.Fin.foldl_eq_foldlTR

public theorem Nat.recCompiled {motive : Nat → Sort u} (zero : motive 0)
    (step : (n : Nat) → motive n → motive (n + 1)) (n : Nat) :
    OmegaChecks.InitPort.Alternatives.Nat.recCompiled zero step n =
      _root_.Nat.recCompiled zero step n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (step n) ih

public theorem Nat.repeatTR {α : Type u} (f : α → α) (n : Nat) (x : α) :
    OmegaChecks.InitPort.Alternatives.Nat.repeatTR f n x = _root_.Nat.repeatTR f n x :=
  congrArg (fun k => @k α f n x) _root_.Nat.repeat_eq_repeatTR

public theorem Nat.foldTR {α : Type u} (n : Nat) (f : (i : Nat) → i < n → α → α) (x : α) :
    OmegaChecks.InitPort.Alternatives.Nat.foldTR n f x = _root_.Nat.foldTR n f x :=
  congrArg (fun k => @k α n f x) _root_.Nat.fold_eq_foldTR

public theorem Nat.anyTR (n : Nat) (f : (i : Nat) → i < n → Bool) :
    OmegaChecks.InitPort.Alternatives.Nat.anyTR n f = _root_.Nat.anyTR n f :=
  congrArg (fun k => @k n f) _root_.Nat.any_eq_anyTR

public theorem Nat.allTR (n : Nat) (f : (i : Nat) → i < n → Bool) :
    OmegaChecks.InitPort.Alternatives.Nat.allTR n f = _root_.Nat.allTR n f :=
  congrArg (fun k => @k n f) _root_.Nat.all_eq_allTR

public theorem Nat.decidableBallLTTR (n : Nat) (P : ∀ k, k < n → Prop)
    [inst : ∀ k h, Decidable (P k h)] :
    @_root_.Nat.decidableBallLT n P inst =
      @_root_.Nat.decidableBallLTTR n P inst := Subsingleton.elim ..

public theorem Nat.decidableExistsLTTR {p : Nat → Prop} [inst : DecidablePred p] (n : Nat) :
    @_root_.Nat.decidableExistsLT p inst n =
      @_root_.Nat.decidableExistsLTTR p inst n := Subsingleton.elim ..

public theorem Nat.decidableExistsLT'TR {n : Nat} {p : (m : Nat) → m < n → Prop}
    [inst : ∀ m h, Decidable (p m h)] :
    @_root_.Nat.decidableExistsLT' n p inst =
      @_root_.Nat.decidableExistsLT'TR n p inst := Subsingleton.elim ..

end OmegaChecks.Interface.Equations

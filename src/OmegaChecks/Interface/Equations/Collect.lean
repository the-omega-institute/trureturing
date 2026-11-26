module

public import OmegaChecks.InitPort.Alternatives.Collect
import all OmegaChecks.InitPort.Alternatives.Collect
import all Init.Data.Iterators.Consumers.Monadic.Collect

/-! The finite collectors run the same step function as the general official collectors. -/

open Std Std.Iterators
namespace OmegaChecks.Interface.Equations

public theorem Std.IterM.Total.toArray {α : Type u} {m : Type u → Type v} {β : Type u}
    [Monad m] [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) :
    OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toArray it = it.toArray := by
  unfold OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toArray
    _root_.Std.IterM.Total.toArray IterM.toArray IterM.toArray.go
  rw [WellFounded.extrinsicFix₂_eq_fix (OmegaChecks.InitPort.Alternatives.collectorWF (σ := Array β))]
  congr 1
  funext p recur
  congr 1
  funext step
  cases step.inflate using PlausibleIterStep.casesOn <;> rfl

public theorem Std.IterM.Total.toListRev {α : Type u} {m : Type u → Type v} {β : Type u} [Monad m]
    [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) :
    OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toListRev it = it.toListRev := by
  unfold OmegaChecks.InitPort.Alternatives.Std.IterM.Total.toListRev
    _root_.Std.IterM.Total.toListRev IterM.toListRev IterM.toListRev.go
  rw [WellFounded.extrinsicFix₂_eq_fix (OmegaChecks.InitPort.Alternatives.collectorWF (σ := List β))]
  congr 1
  funext p recur
  congr 1
  funext step
  cases step.inflate using PlausibleIterStep.casesOn <;> rfl

end OmegaChecks.Interface.Equations

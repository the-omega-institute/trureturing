module
public import OmegaChecks.InitPort.Alternatives.Option.Loop
import all OmegaChecks.InitPort.Alternatives.Option.Loop
import all Init.Data.Option.Instances

namespace OmegaChecks.Interface.Equations
public theorem Option.instForIn'InferInstanceMembershipOfMonad.{u,v,w}
    {m : Type u → Type v} {α : Type w} [Monad m] :
    @OmegaChecks.InitPort.Alternatives.Option.instForIn'InferInstanceMembershipOfMonad m α _ =
      @_root_.Option.instForIn'InferInstanceMembershipOfMonad m α _ := by
  unfold OmegaChecks.InitPort.Alternatives.Option.instForIn'InferInstanceMembershipOfMonad
    OmegaChecks.InitPort.Alternatives.optionLoop _root_.Option.instForIn'InferInstanceMembershipOfMonad
  congr 1
  funext β o init f
  cases o with
  | none => rfl
  | some a =>
    apply congrArg (fun k => f a rfl init >>= k)
    funext step
    cases step <;> rfl
end OmegaChecks.Interface.Equations

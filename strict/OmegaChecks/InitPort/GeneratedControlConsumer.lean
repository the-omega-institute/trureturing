module
prelude
public import OmegaInit.Control.Except
public import OmegaInit.Control.Option
public import OmegaInit.Control.State

@[export omega_generated_except]
public def exceptResult (x y : Omega.Bool) : Omega.Bool :=
  let action : Omega.ExceptT Omega.Bool Omega.Id Omega.Bool :=
    Omega.Bool.casesOn (motive := fun _ => Omega.Except Omega.Bool Omega.Bool) x (.error y) (.ok x)
  @Omega.ExceptT.runK Omega.Id Omega.Bool Omega.Bool Omega.Bool Omega.Id.instMonad action
    (fun a => a) (fun b => b)

@[export omega_generated_option]
public def optionResult (x y : Omega.Bool) : Omega.Bool :=
  let action : Omega.OptionT Omega.Id Omega.Bool :=
    Omega.Bool.casesOn (motive := fun _ => Omega.Option Omega.Bool) x .none (.some y)
  let result := @Omega.OptionT.tryCatch Omega.Id Omega.Id.instMonad Omega.Bool action
    (fun (_ : Omega.PUnit.{1}) => Omega.Option.some .false)
  (Omega.OptionT.run result).getD .false

@[export omega_generated_state]
public def stateResult (x y : Omega.Bool) : Omega.Bool :=
  let first := @Omega.StateT.modifyGet Omega.Bool Omega.Id Omega.Id.instMonad Omega.Bool
    (fun old => Omega.Prod.mk old y)
  let computation := @Omega.StateT.bind Omega.Bool Omega.Id Omega.Id.instMonad Omega.Bool Omega.Bool first
    (fun a => @Omega.StateT.modifyGet Omega.Bool Omega.Id Omega.Id.instMonad Omega.Bool
      (fun afterFirst => Omega.Prod.mk (Omega.strictAnd a afterFirst) afterFirst))
  (Omega.StateT.run computation x).fst

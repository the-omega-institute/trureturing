module
prelude
public import OmegaInit.System.ST

private def flipBit (a : Omega.Bool) : Omega.Bool :=
  Omega.Bool.casesOn (motive := fun _ => Omega.Bool) a .true .false

@[export omega_pure_state]
public def pureState (a : Omega.Bool) : Omega.Bool :=
  Omega.runST fun σ =>
    @Omega.ST.bind σ _ _ (Omega.ST.pure a) fun value => Omega.ST.pure (flipBit value)

@[export omega_pure_exception_state]
public def exceptionState (raise recover a : Omega.Bool) : Omega.Except Omega.Bool Omega.Bool :=
  Omega.runEST fun σ =>
    let action := Omega.Bool.casesOn (motive := fun _ => Omega.EST Omega.Bool σ Omega.Bool)
      raise (Omega.EST.pure a) (Omega.EST.throw a)
    let bound := Omega.EST.bind action fun value => Omega.EST.pure (flipBit value)
    Omega.EST.tryCatch bound fun err =>
      Omega.Bool.casesOn (motive := fun _ => Omega.EST Omega.Bool σ Omega.Bool)
        recover (Omega.EST.throw err) (Omega.EST.pure err)

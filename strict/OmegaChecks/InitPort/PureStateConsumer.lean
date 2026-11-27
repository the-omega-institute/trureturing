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

@[export omega_state_instances]
public def stateInstances (a : Omega.Bool) : Omega.Bool :=
  Omega.runST fun σ =>
    let m := Omega.instMonadST σ
    let bind := @Omega.Bind.bind (Omega.ST σ) (@Omega.Monad.toBind _ m)
    let x := @Omega.Inhabited.default (Omega.ST σ Omega.Bool) (@Omega.instInhabitedST σ _ ⟨a⟩)
    let attached := @Omega.MonadAttach.attach (Omega.ST σ) Omega.instMonadAttachST _ x
    let result := @Omega.MonadFinally.tryFinally' (Omega.ST σ) Omega.instMonadFinallyST _ _ attached fun opt =>
      Omega.Option.casesOn (motive := fun _ => Omega.ST σ Omega.Bool) opt
        (Omega.ST.pure .false) (fun entry => Omega.ST.pure (flipBit entry.val))
    bind result fun pair => Omega.ST.pure pair.snd

@[export omega_exception_instances]
public def exceptionInstances (raise recover a : Omega.Bool) : Omega.Except Omega.Bool Omega.Bool :=
  Omega.runEST fun σ =>
    let M := Omega.EST Omega.Bool σ
    let m := Omega.instMonadEST Omega.Bool σ
    let bind := @Omega.Bind.bind M (@Omega.Monad.toBind _ m)
    let except := Omega.instMonadExceptOfEST Omega.Bool σ
    let lift := @Omega.MonadLift.monadLift (Omega.ST σ) M Omega.instMonadLiftSTEST
    let failed := @Omega.Inhabited.default (M Omega.Bool) (@Omega.instInhabitedEST Omega.Bool σ _ ⟨a⟩)
    let action := Omega.Bool.casesOn (motive := fun _ => M Omega.Bool) raise (lift (Omega.ST.pure a)) failed
    let attached := @Omega.MonadAttach.attach M Omega.instMonadAttachEST _ action
    let result := @Omega.MonadFinally.tryFinally' M Omega.instMonadFinallyEST _ _ attached fun opt =>
      Omega.Option.casesOn (motive := fun _ => M Omega.Bool) opt
        (@Omega.MonadExceptOf.throw _ M except _ (flipBit a)) (fun entry => Omega.EST.pure (flipBit entry.val))
    @Omega.MonadExceptOf.tryCatch _ M except _ (bind result fun pair => Omega.EST.pure pair.snd) fun err =>
      Omega.Bool.casesOn (motive := fun _ => M Omega.Bool) recover (Omega.EST.throw err) (Omega.EST.pure err)

private abbrev Output := Omega.EST.Out Omega.Bool Omega.Unit Omega.Bool

@[noinline] private def okAt (out : Output) (h : Omega.Eq out.ctorIdx .zero) : Omega.Bool :=
  Omega.EST.Out.ok.elim (motive := fun _ => Omega.Bool) out h fun a _ => flipBit a

@[noinline] private def errorAt (out : Output) (h : Omega.Eq out.ctorIdx (.succ .zero)) : Omega.Bool :=
  Omega.EST.Out.error.elim (motive := fun _ => Omega.Bool) out h fun a _ => a

@[export omega_state_elim]
public def eliminateOutput (raise a : Omega.Bool) : Omega.Bool :=
  let world := Omega.Void.mk (Omega.PUnit.unit : Omega.Unit)
  Omega.Bool.casesOn (motive := fun _ => Omega.Bool) raise
    (okAt (.ok a world) (.refl _)) (errorAt (.error a world) (.refl _))

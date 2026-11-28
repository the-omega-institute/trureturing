module
public import Init.System.IO

namespace OmegaChecks.InitBoundaries.EffectObservations

private theorem differentReads {α β : Type} (read : α → β) (x : α) {a b : β}
    (before : read x = a) (after : read x = b) (different : a ≠ b) : False :=
  different (before.symm.trans after)

public theorem base (run : type_of% @unsafeBaseIO) (action : BaseIO Nat) (n : Nat)
    (before : run action = n) (after : run action = n+1) : False :=
  differentReads (@run Nat) action before after (Nat.ne_of_lt (Nat.lt_succ_self n))

public theorem eio (run : type_of% @unsafeEIO) (action : EIO Unit Nat) (n : Nat)
    (before : run action = .ok n) (after : run action = .ok (n+1)) : False :=
  differentReads (fun a : EIO Unit Nat => run a) action before after
    (fun h => Nat.ne_of_lt (Nat.lt_succ_self n) (Except.ok.inj h))

public theorem io (run : type_of% @unsafeIO) (action : IO Nat) (n : Nat)
    (before : run action = .ok n) (after : run action = .ok (n+1)) : False :=
  differentReads (fun a : IO Nat => run a) action before after
    (fun h => Nat.ne_of_lt (Nat.lt_succ_self n) (Except.ok.inj h))

-- Use distinct calls around the cell write, with the same action at both observations.
@[noinline] private unsafe def sampleBase (action : BaseIO Nat) (tick : Nat) : IO (Nat × Nat) :=
  pure (tick, unsafeBaseIO action)
@[noinline] private unsafe def sampleE (action : EIO Unit Nat) (tick : Nat) : IO (Nat × Except Unit Nat) :=
  pure (tick, unsafeEIO action)
@[noinline] private unsafe def sampleIO (action : IO Nat) (tick : Nat) : IO (Nat × Except IO.Error Nat) :=
  pure (tick, unsafeIO action)

public unsafe def observe (n : Nat) : IO (List String) := do
  let cell ← IO.mkRef n
  let get : BaseIO Nat := cell.get
  let getE : EIO Unit Nat := liftM get
  let getIO : IO Nat := liftM get
  let (_, b₁) ← sampleBase get n
  let (_, e₁) ← sampleE getE n
  let (_, i₁) ← sampleIO getIO n
  cell.set (n+1)
  let (_, b₂) ← sampleBase get (n+1)
  let (_, e₂) ← sampleE getE (n+1)
  let (_, i₂) ← sampleIO getIO (n+1)
  let results := [("unsafeBaseIO", b₁ == n && b₂ == n+1),
    ("unsafeEIO", e₁.toOption == some n && e₂.toOption == some (n+1)),
    ("unsafeIO", i₁.toOption == some n && i₂.toOption == some (n+1))]
  return (results.filter Prod.snd).map Prod.fst

end OmegaChecks.InitBoundaries.EffectObservations

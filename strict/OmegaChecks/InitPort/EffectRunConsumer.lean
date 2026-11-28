module
prelude
public import OmegaInit.System.IO

public structure ReadActions where
  base : Omega.BaseIO Omega.Nat
  eio : Omega.EIO Omega.Nat Omega.Nat
  io : Omega.IO Omega.Nat

@[export omega_effect_readers]
public def readers (r : Omega.ST.Ref Omega.IO.RealWorld Omega.Nat) : ReadActions :=
  let read : Omega.BaseIO Omega.Nat := fun world =>
    let before := Omega.ST.Prim.Ref.swap r Omega.Nat.zero world
    let after := Omega.ST.Prim.Ref.set r before.val before.state
    ⟨before.val, after.state⟩
  ⟨read, Omega.BaseIO.toEIO read, Omega.BaseIO.toEIO read⟩

@[export omega_effect_base]
public unsafe def runBase (r : ReadActions) := Omega.unsafeBaseIO r.base

@[export omega_effect_eio]
public unsafe def runEIO (r : ReadActions) := Omega.unsafeEIO r.eio

@[export omega_effect_io]
public unsafe def runIO (r : ReadActions) := Omega.unsafeIO r.io

@[export omega_effect_eio_error]
public unsafe def runEIOError (err : Omega.Nat) : Omega.Except Omega.Nat Omega.Nat :=
  Omega.unsafeEIO (fun s => Omega.EST.Out.error err s)

@[export omega_effect_io_error]
public unsafe def runIOError (err : Omega.IO.Error) : Omega.Except Omega.IO.Error Omega.Nat :=
  Omega.unsafeIO (fun s => Omega.EST.Out.error err s)

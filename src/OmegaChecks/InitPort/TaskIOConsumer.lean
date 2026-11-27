module
prelude
public import OmegaInit.System.IO

@[export omega_io_smoke_state] public def taskState {α : Type} (t : Omega.Task α) :=
  Omega.IO.getTaskState t

@[export omega_io_smoke_finished] public def finished {α : Type} (t : Omega.Task α) :=
  Omega.IO.hasFinished t

@[export omega_io_smoke_wait] public def waitTask {α : Type} (t : Omega.Task α) :=
  Omega.IO.wait t

@[export omega_io_smoke_any] public def waitForEither {α : Type} (t u : Omega.Task α) :
    Omega.BaseIO α :=
  Omega.IO.waitAny (Omega.List.cons t (Omega.List.cons u Omega.List.nil)) (Omega.Nat.zero_lt_succ _)

@[export omega_io_smoke_cancel] public def cancelTask {α : Type} (t : Omega.Task α) := Omega.IO.cancel t

@[export omega_io_smoke_canceled] public def canceled (world : Omega.Void Omega.IO.RealWorld) :=
  Omega.IO.checkCanceled world

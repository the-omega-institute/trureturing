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

@[export omega_io_smoke_launch] public def launch {α : Type} (act : Omega.BaseIO α) :=
  Omega.BaseIO.asTask act (Omega.Nat.succ Omega.Nat.zero)

@[export omega_io_smoke_map] public def mapTask {α : Type} (t : Omega.Task α) :=
  Omega.BaseIO.mapTask (fun a world => ⟨Omega.Option.some a, world⟩) t Omega.Nat.zero Omega.Bool.false

@[export omega_io_smoke_bind] public def bindTask {α : Type} (t : Omega.Task α) :=
  Omega.BaseIO.bindTask t (fun a world => ⟨Omega.Task.pure (Omega.Option.some a), world⟩)
    Omega.Nat.zero Omega.Bool.true

@[export omega_io_smoke_chain] public def chainAfter {α : Type}
    (t : Omega.Task α) (after : α → Omega.BaseIO Omega.Unit) :=
  Omega.BaseIO.chainTask t after Omega.Nat.zero Omega.Bool.false

@[export omega_io_smoke_collect] public def collectTasks {α : Type} (ts : Omega.List (Omega.Task α))
    (sync : Omega.Bool) :=
  Omega.BaseIO.mapTasks (fun xs world => ⟨xs, world⟩) ts Omega.Nat.zero sync

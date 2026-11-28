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

@[export omega_smoke_EIO_launch] public def launchEIO {ε α : Type} (act : Omega.EIO ε α) :=
  Omega.EIO.asTask act Omega.Nat.zero

@[export omega_smoke_EIO_map] public def mapEIO {ε α : Type} (act : α → Omega.EIO ε α) (t : Omega.Task α) :=
  Omega.EIO.mapTask act t Omega.Nat.zero Omega.Bool.true

@[export omega_smoke_EIO_bind] public def bindEIO {ε α : Type}
    (t : Omega.Task α) (act : α → Omega.EIO ε (Omega.Task (Omega.Except ε α))) :=
  Omega.EIO.bindTask t act Omega.Nat.zero Omega.Bool.true

@[export omega_smoke_EIO_chain] public def chainEIO {ε α : Type}
    (t : Omega.Task α) (act : α → Omega.EIO ε Omega.Unit) :=
  Omega.EIO.chainTask t act Omega.Nat.zero Omega.Bool.true

@[export omega_smoke_EIO_many] public def manyEIO {ε α : Type}
    (act : Omega.List α → Omega.EIO ε α) (ts : Omega.List (Omega.Task α)) :=
  Omega.EIO.mapTasks act ts Omega.Nat.zero Omega.Bool.true

@[export omega_smoke_IO_launch] public def launchIO {α : Type} (act : Omega.IO α) :=
  Omega.IO.asTask act Omega.Nat.zero

@[export omega_smoke_IO_map] public def mapIO {α : Type} (act : α → Omega.IO α) (t : Omega.Task α) :=
  Omega.IO.mapTask act t Omega.Nat.zero Omega.Bool.true

@[export omega_smoke_IO_bind] public def bindIO {α : Type}
    (t : Omega.Task α) (act : α → Omega.IO (Omega.Task (Omega.Except Omega.IO.Error α))) :=
  Omega.IO.bindTask t act Omega.Nat.zero Omega.Bool.true

@[export omega_smoke_IO_chain] public def chainIO {α : Type}
    (t : Omega.Task α) (act : α → Omega.IO Omega.Unit) :=
  Omega.IO.chainTask t act Omega.Nat.zero Omega.Bool.true

@[export omega_smoke_IO_many] public def manyIO {α : Type}
    (act : Omega.List α → Omega.IO α) (ts : Omega.List (Omega.Task α)) :=
  Omega.IO.mapTasks act ts Omega.Nat.zero Omega.Bool.true

@[export omega_io_end_of_file] public def endOfFile (_ : Omega.Unit) := Omega.IO.Error.unexpectedEof

@[export omega_io_smoke_remaining] public def firstWithRemaining {α : Type}
    (head : Omega.Task α) (tail : Omega.List (Omega.Task α)) :=
  Omega.IO.waitAny' (Omega.List.cons head tail) (Omega.Nat.zero_lt_succ _)

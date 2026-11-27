module
prelude
public import OmegaInit.System.Promise

@[export omega_smoke_new] public def allocate {α : Type} (h : Omega.Nonempty α)
    (s : Omega.Void Omega.IO.RealWorld) : Omega.ST.Out Omega.IO.RealWorld (Omega.IO.Promise α) :=
  @Omega.IO.Promise.new α h s

@[export omega_smoke_resolve] public def resolve {α : Type} (x : α) (p : Omega.IO.Promise α)
    (s : Omega.Void Omega.IO.RealWorld) : Omega.ST.Out Omega.IO.RealWorld Omega.Unit :=
  Omega.IO.Promise.resolve x p s

@[export omega_smoke_is_resolved] public def isResolved {α : Type} (p : Omega.IO.Promise α)
    (s : Omega.Void Omega.IO.RealWorld) : Omega.ST.Out Omega.IO.RealWorld Omega.Bool :=
  p.isResolved s

@[export omega_smoke_result] public def result {α : Type} (p : Omega.IO.Promise α) :
    Omega.Task (Omega.Option α) := p.result?

@[export omega_smoke_default] public def resultD {α : Type} (p : Omega.IO.Promise α) (fallback : α) :
    Omega.Task α := p.resultD fallback

@[export omega_smoke_task_get] public def read {α : Type} (task : Omega.Task α) : α := task.get

@[export omega_smoke_task_pattern] public def readPattern {α : Type} (task : Omega.Task α) : α :=
  match task with | Omega.Task.pure value => value

@[export omega_smoke_task_pure] public def pureTask {α : Type} (value : α) : Omega.Task α :=
  Omega.Task.pure value

-- Generalized field notation resolves methods through the physical structure namespace.
#check fun (t : Omega.Task Omega.Bool) =>
  (t.map (fun x => x) Omega.Task.Priority.default Omega.false : Omega.Task Omega.Bool)
#check fun (t : Omega.Task Omega.Bool) =>
  (t.bind (fun x => Omega.Task.pure x) Omega.Task.Priority.default Omega.false : Omega.Task Omega.Bool)

-- These calls exercise the literal binder annotations used by ordinary elaboration.
example (task : Omega.Task Omega.Bool) (f : Omega.Bool → Omega.Bool) :
    Omega.Eq (task.map f) (task.map f Omega.Task.Priority.default Omega.false) := Omega.rfl

example (task : Omega.Task Omega.Bool) (f : Omega.Bool → Omega.Task Omega.Bool) :
    Omega.Eq (task.bind f) (task.bind f Omega.Task.Priority.default Omega.false) := Omega.rfl

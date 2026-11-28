module
prelude
public import OmegaInit.Core

@[export omega_task_smoke_spawn] public def startTask {α : Type} (value : α) : Omega.Task α :=
  Omega.Task.spawn (fun _ => value) Omega.Task.Priority.dedicated

@[export omega_task_smoke_map] public def mapTask {α β : Type} (task : Omega.Task α) (value : β) :
    Omega.Task β := task.map (fun _ => value) Omega.Task.Priority.max Omega.false

@[export omega_task_smoke_bind] public def bindTask {α : Type} (task : Omega.Task α) :
    Omega.Task α := task.bind (fun value => Omega.Task.pure value) Omega.Task.Priority.default Omega.true

@[export omega_task_smoke_read] public def readTask {α : Type} (task : Omega.Task α) : α := task.get

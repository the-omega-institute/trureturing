module
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.Compiler.LCNF.MonoTypes
import all Init.System.IO
import Lean

open Lean OmegaChecks.InitPort.NativeState

private def entries := #[(`IO.getTaskState, "get_task_state"), (`IO.hasFinished, "task_has_finished"),
  (`IO.wait, "wait"), (`IO.waitAny, "wait_any"), (`IO.waitAny', "wait_any_rest"), (`IO.cancel, "cancel"), (`IO.checkCanceled, "check_canceled"),
  (`BaseIO.asTask, "as_task"), (`BaseIO.mapTask, "map_task"), (`BaseIO.bindTask, "bind_task"),
  (`BaseIO.chainTask, "chain_task"), (`BaseIO.mapTasks, "map_tasks")]

private def exceptionOperations := #[(`asTask, "as_task"), (`mapTask, "map_task"), (`bindTask, "bind_task"),
  (`chainTask, "chain_task"), (`mapTasks, "map_tasks")]

private def exceptionEntries : Array (Name × String) := Id.run do
  let mut result := #[]
  for owner in #[`EIO, `IO] do
    for (op, suffix) in exceptionOperations do result := result.push (owner ++ op, "except_" ++ suffix)
  return result

-- The IO scheduling operations specialize the polymorphic exception type.
example : @IO.asTask = @EIO.asTask IO.Error := rfl
example {α β : Type} : @IO.mapTask α β = @EIO.mapTask α IO.Error β := rfl
example {α β : Type} : @IO.bindTask α β = @EIO.bindTask α IO.Error β := rfl
example {α β : Type} : @IO.mapTasks α β = @EIO.mapTasks α IO.Error β := rfl
example {α : Type} : @IO.chainTask α = @EIO.chainTask α IO.Error := rfl

private def inputs (name : Name) (strict : Bool) : Array (IR.IRType × Bool) :=
  let world := (if strict then IR.IRType.tobject else .void, false)
  let op := name.getString!
  let errorParam : Array (IR.IRType × Bool) := if name.getPrefix == `EIO then #[(.erased, false)] else #[]
  if op == "asTask" then errorParam ++ #[(.erased, false), (.object, false), (.tobject, false), world]
  else if op == "mapTask" || op == "bindTask" then
    errorParam ++ #[(.erased, false), (.erased, false), (.object, false), (.object, false), (.tobject, false), (.uint8, false), world]
  else if op == "chainTask" then
    errorParam ++ #[(.erased, false), (.object, false), (.object, false), (.tobject, false), (.uint8, false), world]
  else if op == "mapTasks" then
    errorParam ++ #[(.erased, false), (.erased, false), (.object, false), (.tobject, false), (.tobject, false), (.uint8, false), world]
  else if name == `IO.checkCanceled then #[world]
  else if name == `IO.waitAny || name == `IO.waitAny' then
    #[(.erased, false), (.tobject, name == `IO.waitAny), (.erased, false), world]
  else #[(.erased, false), (.object, name != `IO.wait && !(name == `IO.hasFinished && strict)), world]

private def checkLayouts (env : Environment) (names : Array Name) : IO Unit := do
  let check (n : Name) (tag fields : Nat) := do
    let some layout := Compiler.LCNF.ctorLayoutExt.find? env n | throw <| IO.userError s!"missing task I/O layout {n}"
    unless layout.ctorInfo.cidx == tag && layout.ctorInfo.size == fields && layout.ctorInfo.usize == 0 &&
        layout.ctorInfo.ssize == 0 && layout.fieldInfo.size == fields do
      throw <| IO.userError s!"mismatched task I/O layout {n}"
  if names.contains `Omega.IO.getTaskState then
    for (n, tag) in #[(`Omega.IO.TaskState.waiting, 0), (`Omega.IO.TaskState.running, 1), (`Omega.IO.TaskState.finished, 2)] do
      check n tag 0
  let exceptions := names.any fun n => exceptionEntries.any fun (op, _) => n == `Omega ++ op
  let schedules := exceptions || names.any (`Omega.BaseIO).isPrefixOf
  if schedules then checkNativeNat env
  if schedules || names.contains `Omega.IO.hasFinished || names.contains `Omega.IO.checkCanceled then
    check `Bool.false 0 0
    check `Bool.true 1 0
  if exceptions then
    for (n, tag) in #[(`Omega.EST.Out.ok, 0), (`Omega.EST.Out.error, 1)] do
      check n tag 2
      let some layout := Compiler.LCNF.ctorLayoutExt.find? env n | throw <| IO.userError s!"missing {n}"
      let #[.object 0 _, .object 1 _] := layout.fieldInfo | throw <| IO.userError s!"unexpected {n} field order"
    check `Omega.Except.error 0 1
    check `Omega.Except.ok 1 1
  if names.contains `Omega.IO.waitAny' then
    check `Omega.Prod.mk 0 2
    let some pair := Compiler.LCNF.ctorLayoutExt.find? env `Omega.Prod.mk | throw <| IO.userError "missing wait result pair"
    let #[.object 0 _, .object 1 _] := pair.fieldInfo | throw <| IO.userError "incorrect pair field order"
  unless names.contains `Omega.IO.waitAny || names.contains `Omega.IO.waitAny' || names.any (·.getString! == "mapTasks") do return
  check `Omega.List.nil 0 0
  check `Omega.List.cons 1 2
  let some cons := Compiler.LCNF.ctorLayoutExt.find? env `Omega.List.cons | throw <| IO.userError "missing task list"
  let #[.object 0 _, .object 1 _] := cons.fieldInfo | throw <| IO.userError "incorrect task list field order"

public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and native C output"
  let original ← importModules #[{module := `Init.System.IO}] {}
  let entries := entries ++ exceptionEntries
  for (n, sym) in entries do
    if sym.startsWith "except_" || n == `IO.waitAny' || n == `IO.hasFinished || n == `BaseIO.chainTask || n == `BaseIO.mapTasks then
      let ret := if n == `IO.hasFinished then IR.IRType.uint8 else if n == `BaseIO.chainTask then .tagged else .object
      let some (.fdecl _ ps result _ _) := IR.findEnvDecl original n | throw <| IO.userError s!"missing compiled {n}"
      let args := inputs n false
      unless ps.map (fun p => (p.ty, p.borrow)) == args && result == ret do throw <| IO.userError s!"{n} ABI changed"
      let some (.fdecl _ reduced result _ _) := IR.findEnvDecl original (n ++ `_redArg)
        | throw <| IO.userError s!"missing reduced {n}"
      unless reduced.map (fun p => (p.ty, p.borrow)) == args.filter (·.1 != .erased) && result == ret do
        throw <| IO.userError s!"unexpected reduced {n} ABI"
    else
      let ret := if (`BaseIO).isPrefixOf n then IR.IRType.object
        else if n == `IO.cancel then .tagged
        else if n == `IO.wait || n == `IO.waitAny then .tobject else .uint8
      verify original n (inputs n false) ret ("lean_io_" ++ sym)
  searchPathRef.set [lib]
  let owner := `OmegaInit.System.IO
  let imports := #[{module := owner : Import}]
  let env ← importModules imports {}
  let names := (entries.map fun (n, _) => `Omega ++ n).filter env.contains
  if names.isEmpty then return
  installStateLayout lib env
  let env ← importModules imports {}
  if names.contains `Omega.IO.getTaskState then
    writeCode lib owner (← compileLayouts env `Omega.IO.TaskState) layouts
  if names.any (fun n => exceptionEntries.any fun (op, _) => n == `Omega ++ op) then
    let needsError := names.any fun n => n.getPrefix == `Omega.IO && exceptionEntries.any fun (op, _) => n == `Omega ++ op
    let types := (if needsError then #[`Omega.Fin, `Omega.BitVec, `Omega.UInt32, `Omega.UInt8, `Omega.Array,
      `Omega.ByteArray, `Omega.String, `Omega.IO.Error] else #[]) ++ #[`Omega.EST.Out, `Omega.Except]
    for n in types do
      let env ← importModules imports {}
      if (Compiler.LCNF.monoTypeExt.find? env n).isSome then continue
      let some idx := env.getModuleIdxFor? n | throw <| IO.userError s!"missing layout owner {n}"
      writeCode lib env.header.moduleNames[idx]! (← compileLayouts env n) layouts
  let env ← importModules imports {}
  checkLayouts env names
  let compiled ← compile (← localEnv env owner names) do
    for (n, suffix) in entries do
      let target := `Omega ++ n
      if names.contains target then
        modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := target) e (target, ⟨[.standard `all ("omega_io_" ++ suffix)]⟩)
        (← compileDeclsRef.get) #[target] {}
  for (n, suffix) in entries do
    if names.contains (`Omega ++ n) then verify compiled (`Omega ++ n) (inputs n true) .object ("omega_io_" ++ suffix)
  writeCode lib owner compiled codeExtensions
  emitBridge compiled owner "src/OmegaChecks/InitPort/task_io_runtime.c" output

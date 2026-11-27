module
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState
import all Lean.Compiler.LCNF.ToImpureType
import Lean

open Lean OmegaChecks.InitPort.NativeState

private def entries := #[(`IO.getTaskState, "get_task_state"), (`IO.hasFinished, "task_has_finished"),
  (`IO.wait, "wait"), (`IO.waitAny, "wait_any"), (`IO.cancel, "cancel"), (`IO.checkCanceled, "check_canceled")]

private def inputs (name : Name) (strict : Bool) : Array (IR.IRType × Bool) :=
  let world := (if strict then IR.IRType.tobject else .void, false)
  if name == `IO.checkCanceled then #[world]
  else if name == `IO.waitAny then #[(.erased, false), (.tobject, true), (.erased, false), world]
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
  if names.contains `Omega.IO.hasFinished || names.contains `Omega.IO.checkCanceled then
    check `Omega.Bool.false 0 0
    check `Omega.Bool.true 1 0
  unless names.contains `Omega.IO.waitAny do return
  check `Omega.List.nil 0 0
  check `Omega.List.cons 1 2
  let some cons := Compiler.LCNF.ctorLayoutExt.find? env `Omega.List.cons | throw <| IO.userError "missing task list"
  let #[.object 0 _, .object 1 _] := cons.fieldInfo | throw <| IO.userError "incorrect task list field order"

public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and native C output"
  let original ← importModules #[{module := `Init.System.IO}] {}
  for (n, sym) in entries do
    if n == `IO.hasFinished then
      let some (.fdecl _ ps .uint8 _ _) := IR.findEnvDecl original n | throw <| IO.userError "missing compiled task query"
      unless ps.map (fun p => (p.ty, p.borrow)) == inputs n false do throw <| IO.userError "task query ABI changed"
      let some (.fdecl _ reduced .uint8 _ _) := IR.findEnvDecl original `IO.hasFinished._redArg
        | throw <| IO.userError "missing reduced task query"
      unless reduced.map (fun p => (p.ty, p.borrow)) == #[(.object, true), (.void, false)] do
        throw <| IO.userError "unexpected borrowed task query"
    else
      let ret := if n == `IO.cancel then IR.IRType.tagged
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

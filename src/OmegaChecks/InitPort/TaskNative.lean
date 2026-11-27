module
meta import OmegaChecks.ModuleSurface
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState
import OmegaChecks.ModuleSurface
import Lean
import Lean.Compiler.LCNF.EmitC
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.OriginalConstKind

open Lean
open OmegaChecks.InitPort.NativeState

private def checkTask (env : Environment) : IO Unit := do
  verify env `Task.pure #[(.erased, false), (.tobject, false)] .object "lean_task_pure"
  verify env `Task.get #[(.erased, false), (.object, false)] .tobject "lean_task_get_own"

private def operations := #[(`Task.spawn, "spawn"), (`Task.map, "map"), (`Task.bind, "bind")]

private def priorities := #[`Omega.Task.Priority.default, `Omega.Task.Priority.max, `Omega.Task.Priority.dedicated]

private def operationArgs (n : Name) : Array (IR.IRType × Bool) :=
  if n == `Task.spawn then #[(.erased, false), (.tobject, false), (.tobject, false)]
  else #[(.erased, false), (.erased, false), (if n == `Task.map then .tobject else .object, false),
    (.object, false), (.tobject, false), (.uint8, false)]

private def checkOperands (env : Environment) : IO Unit := do
  let check (n : Name) (tag fields : Nat) := do
    let some d := Compiler.LCNF.ctorLayoutExt.find? env n | throw <| IO.userError s!"missing runtime layout {n}"
    unless d.ctorInfo.cidx == tag && d.ctorInfo.size == fields && d.ctorInfo.usize == 0 &&
        d.ctorInfo.ssize == 0 && d.fieldInfo.size == fields do throw <| IO.userError s!"incorrect task operand layout {n}"
  checkNativeNat env
  check `Bool.false 0 0
  check `Bool.true 1 0

/-- At both visibility levels each surface name resolves to its kernel primitive. -/
private def checkPrimitiveNames (env : Environment) : IO Unit := do
  let env := OmegaChecks.ModuleSurface.withImportedAliases env
  let some idx := env.getModuleIdx? `OmegaInit.Core | throw <| IO.userError "missing task module"
  let some (.inductInfo task) := env.find? `Task | throw <| IO.userError "missing task inductive"
  unless task.ctors == [`Task.pure] && task.numParams == 1 && task.numIndices == 0 do
    throw <| IO.userError "unexpected task inductive"
  for n in OmegaChecks.InitCompiler.RootNames.taskPrimitives do
    unless env.contains n do continue
    let alias := `Omega ++ n
    unless !env.contains alias && env.getModuleIdxFor? n == some idx &&
        ResolveName.resolveGlobalName env {} .anonymous [] alias == [(n, [])] do
      throw <| IO.userError s!"{alias} does not resolve uniquely to {n} in OmegaInit.Core"
  if env.contains `Task.get then
    let some p := env.getProjectionFnInfo? `Task.get | throw <| IO.userError "missing task projection"
    unless p.ctorName == `Task.pure && p.i == 0 do throw <| IO.userError "incorrect task projection"

/-- Generate a consumer whose kernel expression uses a raw projection. Surface field
notation goes through a named projection and exercises a different compiler path. -/
private def compileRawRead (env : Environment) (output : System.FilePath) : IO Unit := do
  let moduleName := `OmegaRawTaskConsumer
  let compiled ← compile (env.setMainModule moduleName) do
    let info ← getConstInfo `Task.get
    let body ← Meta.MetaM.run' <| Meta.forallTelescope info.type fun xs _ =>
      Meta.mkLambdaFVars xs (.proj `Task 0 xs.back!)
    let name := `omegaRawTaskRead
    addDecl <| .defnDecl {
      name, levelParams := info.levelParams, type := info.type
      value := body, hints := .regular 1, safety := .safe }
    (← compileDeclsRef.get) #[name] {}
  let c ← (Compiler.LCNF.emitC moduleName).toIO' {fileName := "<raw task consumer>", fileMap := default} {env := compiled}
  IO.FS.writeFile output c

/-- Preserve the task runtime representation recognized by Lean's projection compiler. -/
public unsafe def main (args : List String) : IO Unit := do
  let [lib, raw, output] := args | throw <| IO.userError "expected strict library, raw consumer and native C outputs"
  let original ← importModules #[{module := `Init.Core}] {}
  checkTask original
  for (n, suffix) in operations do verify original n (operationArgs n) .object ("lean_task_" ++ suffix)
  searchPathRef.set [lib]
  let owner := `OmegaInit.Core
  let env ← importModules #[{module := owner}] {}
  unless env.contains `Task do return
  checkPrimitiveNames (← importModules #[{module := owner}] {} (level := .exported))
  checkPrimitiveNames (← importModules #[{module := owner, importAll := true}] {} (level := .private))
  let names := OmegaChecks.InitCompiler.RootNames.taskPrimitives.filter env.contains
  let context ← localEnv env owner names
  let compiled ← compile context do
    for (n, symbol) in #[(`Task.pure, "lean_task_pure"), (`Task.get, "lean_task_get_own")] do
      if (← getEnv).contains n then
        modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all symbol]⟩)
    (← compileDeclsRef.get) #[`Task] {}
    for n in #[`Task.pure, `Task.get] do
      if (← getEnv).contains n then (← compileDeclsRef.get) #[n] {}
  if names.contains `Task.pure then
    verify compiled `Task.pure #[(.erased, false), (.tobject, false)] .object "lean_task_pure"
  if names.contains `Task.get then
    verify compiled `Task.get #[(.erased, false), (.object, false)] .tobject "lean_task_get_own"
  writeCode lib owner compiled (layouts ++ codeExtensions)
  if names.contains `Task.get then compileRawRead (← importModules #[{module := owner}] {}) raw
  let env ← importModules #[{module := owner}] {}
  let methods := operations.map (fun e => `Omega ++ e.1)
  let localNames := (methods ++ priorities).filter env.contains
  if localNames.isEmpty then return
  checkOperands env
  let context ← localEnv env owner localNames
  let functions ← compile context do
    for (official, suffix) in operations do
      let n := `Omega ++ official
      if localNames.contains n then
        modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all ("omega_task_" ++ suffix)]⟩)
        (← compileDeclsRef.get) #[n] {}
    for n in priorities do
      if localNames.contains n then
        modifyEnv fun e => Lean.privateConstKindsExt.insert e n .defn
        (← compileDeclsRef.get) #[n] {}
  for (n, suffix) in operations do
    if localNames.contains (`Omega ++ n) then
      verify functions (`Omega ++ n) (operationArgs n) .object ("omega_task_" ++ suffix)
  writeCode lib owner functions (codeExtensions ++ #[Lean.privateConstKindsExt.name])
  emitBridge functions owner "src/OmegaChecks/InitPort/task_runtime.c" output

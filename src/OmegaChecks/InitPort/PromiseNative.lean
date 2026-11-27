module
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState
import all Lean.Environment
import Lean
import Lean.Compiler.LCNF.EmitC
import all Lean.Compiler.LCNF.MonoTypes
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF

open OmegaChecks.InitPort.NativeState

namespace PromiseNative

private def owner := `OmegaInit.System.Promise
private def allocation := `Omega.IO.Promise.new
private def resolution := `Omega.IO.Promise.resolve
private def allocationSymbol := "omega_io_promise_new"
private def resolutionSymbol := "omega_io_promise_resolve"
private def resolved := `Omega.IO.Promise.isResolved
private def result := `Omega.IO.Promise.result?
private def resultD := `Omega.IO.Promise.resultD
private def resultDSymbol := "omega_io_promise_result_d"
private def resultSymbol := "lean_io_promise_result_opt"
private def resolvedSymbol := "omega_io_promise_is_resolved"

public unsafe def install (lib output : System.FilePath) : IO Unit := do
  let original ← importModules #[{module := `Init.System.Promise}] {}
  verify original `IO.Promise.new #[(.erased, false), (.erased, false), (.void, false)] .tobject "lean_io_promise_new"
  verify original `IO.Promise.resolve #[(.erased, false), (.tobject, false), (.tobject, true), (.void, false)]
    .tagged "lean_io_promise_resolve"
  verify original `IO.Promise.result? #[(.erased, false), (.tobject, true)] .object resultSymbol
  let some (.fdecl _ params .uint8 _ _) := IR.findEnvDecl original `IO.Promise.isResolved
    | throw <| IO.userError "missing native Promise.isResolved"
  unless params.map (fun p => (p.ty, p.borrow)) == #[(.erased, false), (.tobject, true), (.void, false)] do
    throw <| IO.userError "unexpected pinned Promise.isResolved signature"
  let some (.fdecl _ borrowed .uint8 _ _) := IR.findEnvDecl original `IO.Promise.isResolved._redArg
    | throw <| IO.userError "missing reduced Promise.isResolved"
  unless borrowed.map (fun p => (p.ty, p.borrow)) == #[(.tobject, true), (.void, false)] do
    throw <| IO.userError "unexpected borrowing in the runtime poll entry"
  searchPathRef.set [lib]
  let imports := #[{module := owner : Import}]
  let env ← importModules imports {}
  unless [allocation, resolution, resolved, result, resultD].any env.contains do return
  installStateLayout lib env
  let env ← importModules imports {}
  let some (.inductInfo prom) := env.find? `Omega.IO.Promise | throw <| IO.userError "missing promise type"
  let mut names := #[prom.name] ++ prom.ctors.toArray
  for n in #[allocation, resolution, resolved, result, resultD] do
    if env.contains n then names := names.push n
  let contextEnv ← localEnv env owner names
  let compiled ← compile contextEnv do
    (← compileDeclsRef.get) #[prom.name] {}
    for (n, symbol) in #[ (allocation, allocationSymbol), (resolution, resolutionSymbol), (resolved, resolvedSymbol), (result, resultSymbol), (resultD, resultDSymbol)] do
      unless (← getEnv).contains n do continue
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all symbol]⟩)
      (← compileDeclsRef.get) #[n] {}
  let some (some handle) := impureTrivialStructureInfoExt.find? compiled prom.name
    | throw <| IO.userError "native promise handle must be an unboxed field"
  unless handle.numParams == 1 && handle.fieldIdx == 0 && prom.ctors == [handle.ctorName] do
    throw <| IO.userError "unexpected native promise representation"
  if compiled.contains allocation then
    verify compiled allocation #[(.erased, false), (.erased, false), (.tobject, false)] .object allocationSymbol
  if compiled.contains resolution then
    verify compiled resolution #[(.erased, false), (.tobject, false), (.tobject, true), (.tobject, false)]
      .object resolutionSymbol
  if compiled.contains resolved then
    verify compiled resolved #[(.erased, false), (.tobject, false), (.tobject, false)] .object resolvedSymbol
  if compiled.contains result then
    verify compiled result #[(.erased, false), (.tobject, true)] .object resultSymbol
  if compiled.contains resultD then
    verify compiled resultD #[(.erased, false), (.tobject, false), (.tobject, false)] .object resultDSymbol
  writeCode lib owner compiled (layouts ++ codeExtensions)
  emitBridge compiled owner "src/OmegaChecks/InitPort/promise_runtime.c" output

end PromiseNative

public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and native C output"
  PromiseNative.install lib output

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

namespace ReferenceNative

private def owner := `OmegaInit.System.ST
private def allocation := `Omega.ST.Prim.mkRef
private def symbol := "omega_st_mk_ref"

public unsafe def install (lib output : System.FilePath) : IO Unit := do
  let original ← importModules #[{module := `Init.System.ST}] {}
  verify original `ST.Prim.mkRef #[(.erased, false), (.erased, false), (.tobject, false), (.void, false)]
    .tobject "lean_st_mk_ref"
  searchPathRef.set [lib]
  let imports := #[{module := owner : Import}]
  let env ← importModules imports {}
  unless env.contains allocation do return
  installStateLayout lib env
  let env ← importModules imports {}
  let some (.inductInfo ref) := env.find? `Omega.ST.Ref | throw <| IO.userError "missing reference type"
  let contextEnv ← localEnv env owner (#[ref.name, allocation] ++ ref.ctors.toArray)
  let compiled ← compile contextEnv do
    (← compileDeclsRef.get) #[ref.name] {}
    modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := allocation) e (allocation, ⟨[.standard `all symbol]⟩)
    (← compileDeclsRef.get) #[allocation] {}
  let some (some layout) := impureTrivialStructureInfoExt.find? compiled ref.name
    | throw <| IO.userError "expected an unboxed reference handle"
  unless layout.numParams == 2 && layout.fieldIdx == 0 && ref.ctors == [layout.ctorName] do
    throw <| IO.userError "unexpected strict reference layout"
  verify compiled allocation #[(.erased, false), (.erased, false), (.tobject, false), (.tobject, false)]
    .object symbol
  writeCode lib owner compiled (layouts ++ codeExtensions)
  emitBridge compiled owner "src/OmegaChecks/InitPort/reference_runtime.c" output

end ReferenceNative

public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and native C output"
  ReferenceNative.install lib output

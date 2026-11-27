module
import all Lean.Environment
import Lean.Compiler.LCNF.EmitC
import all Lean.Compiler.LCNF.ToImpureType
import OmegaChecks.InitPort.TypeName
meta import OmegaChecks.InitPort.TypeName
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState

open Lean Compiler.LCNF OmegaChecks.InitPort

public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and C output"
  let owner := `OmegaInit.Dynamic
  let source ← importModules #[{module := `Init.Dynamic, importAll := true}] {} (level := .private)
  searchPathRef.set [lib]
  let imports := #[{module := owner, importAll := true : Import}]
  let read := importModules imports {} (level := .private)
  let env ← read
  let rename (n : Name) :=
    if isPrivateName n then mkPrivateNameCore owner (`Omega ++ privateToUserName n) else `Omega ++ n
  let names := [`TypeName.mk, TypeName.reader].filter fun n => env.contains (rename n)
  if names.isEmpty then return
  for name in #[`Nat, `Omega.List, `Omega.Array, `Omega.Fin, `Omega.BitVec, `Omega.UInt8,
      `Omega.ByteArray, `Omega.String, `Omega.Lean.Name, `Omega.TypeName] do
    let state ← read
    if (impureTypeExt.find? state name).isSome then continue
    let compiled ← NativeState.compileLayouts state name
    let idx := (state.getModuleIdxFor? name).get!
    NativeState.writeCode lib state.header.moduleNames[idx]! compiled NativeState.layouts
  let env ← read
  let mut compiled ← TypeName.nativeEntries source env owner rename fun n => env.contains (rename n)
  for n in names do
    let dest := rename n
    unless TypeName.identityIR env dest do
      throw <| IO.userError s!"mismatched installed type name code {dest}"
    let some signature := getSigCore? compiled impureSigExt dest | throw <| IO.userError s!"missing compiled signature {dest}"
    let #[_, name] := signature.params | throw <| IO.userError s!"invalid type name signature {dest}"
    let identity : Decl .impure := {signature with inlineAttr? := none, value := .code (.inc name.fvarId 1 true false (.return name.fvarId))}
    compiled := recordFinalImpureDecl (saveImpureDeclCore compiled identity) dest
  let state := Environment.ofKernelEnv {compiled.toKernelEnv with header.imports := #[], header.isModule := true}
  let c ← (emitC owner).toIO' {fileName := "<type name entry points>", fileMap := default} {env := state}
  IO.FS.writeFile output c

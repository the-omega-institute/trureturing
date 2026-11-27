module
import all Lean.Environment
import all Lean.OriginalConstKind
import Lean.Compiler.LCNF.PhaseExt
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.Compiler.LCNF.MonoTypes
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState

open Lean Compiler.LCNF OmegaChecks.InitPort.NativeState

public unsafe def main (args : List String) : IO Unit := do
  let [lib, out] := args | throw <| IO.userError "expected strict library and native literal output"
  let official ← importModules #[{module := `Init.Prelude, importAll := true}] {}
  verify official `String.ofList #[(.tobject, false)] .object "lean_string_mk"
  let some (.fdecl _ #[arg] .uint32 _ _) := IR.findEnvDecl official `Char.ofNat
    | throw <| IO.userError "missing pinned Char.ofNat"
  unless arg.ty == .tobject && arg.borrow do throw <| IO.userError "unexpected pinned character conversion"
  searchPathRef.set [lib]
  let owner := `OmegaInit.Prelude
  let read := importModules #[{module := owner, importAll := true : Import}] {}
  let env ← read
  let names := [(`Omega.String.ofList, "omega_string_of_list"), (`Omega.Char.ofNat, "omega_char_of_nat")]
  let names := names.filter fun (n, _) => (env.find? n).any (· matches .defnInfo _) &&
    (getSigCore? env impureSigExt n).isNone
  if names.isEmpty then return
  for n in [`Omega.Nat, `Omega.List, `Omega.Fin, `Omega.BitVec, `Omega.UInt8, `Omega.UInt32,
            `Omega.Char, `Omega.Array, `Omega.ByteArray, `Omega.String] do
    let env ← read
    unless (monoTypeExt.find? env n).isSome do
      let some idx := env.getModuleIdxFor? n | throw <| IO.userError s!"missing literal type {n}"
      writeCode lib env.header.moduleNames[idx]! (← compileLayouts env n) layouts
  let env ← read
  checkPriorityLayout env
  for n in [`Omega.Fin, `Omega.BitVec, `Omega.UInt8, `Omega.UInt32, `Omega.Char,
            `Omega.Array, `Omega.ByteArray, `Omega.String] do
    let some (some field) := impureTrivialStructureInfoExt.find? env n
      | throw <| IO.userError s!"missing literal representation of {n}"
    unless field.fieldIdx == 0 do throw <| IO.userError s!"unexpected representation of {n}"
  let some cons := ctorLayoutExt.find? env `Omega.List.cons | throw <| IO.userError "missing list layout"
  let #[.object 0 _, .object 1 _] := cons.fieldInfo | throw <| IO.userError "incorrect character-list fields"
  unless cons.ctorInfo.cidx == 1 && cons.ctorInfo.size == 2 do throw <| IO.userError "incorrect list tag or size"
  let context ← localEnv env owner (names.map Prod.fst).toArray
  let compiled ← compile context do
    for (n, symbol) in names do
      modifyEnv fun e => privateConstKindsExt.insert e n .defn
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all symbol]⟩)
      (← compileDeclsRef.get) #[n] {}
  for (n, symbol) in names do
    verify compiled n #[(.tobject, false)] .tobject symbol
  writeCode lib owner compiled (codeExtensions ++ #[privateConstKindsExt.name])
  emitBridge compiled owner "src/OmegaChecks/InitPort/literal_runtime.c" out

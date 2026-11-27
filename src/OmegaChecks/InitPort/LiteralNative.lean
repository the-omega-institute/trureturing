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
  let [lib, out, ownerArg] := args | throw <| IO.userError "expected strict library, native output and module"
  let owner := ownerArg.toName
  unless owner == `OmegaInit.Prelude || owner == `OmegaInit.Data.String.Basic do
    throw <| IO.userError s!"unsupported string owner {owner}"
  let official ← importModules #[{module := owner.replacePrefix `OmegaInit `Init, importAll := true}] {}
  verify official `String.ofList #[(.tobject, false)] .object "lean_string_mk"
  let some (.fdecl _ #[arg] .uint32 _ _) := IR.findEnvDecl official `Char.ofNat
    | throw <| IO.userError "missing pinned Char.ofNat"
  unless arg.ty == .tobject && arg.borrow do throw <| IO.userError "unexpected pinned character conversion"
  verify official `String.utf8ByteSize #[(.object, true)] .tagged "lean_string_utf8_byte_size"
  let borrowedPair := #[(IR.IRType.object, true), (.object, true)]
  verify official `String.toByteArray #[(.object, false)] .object "lean_string_to_utf8"
  verify official `String.decEq borrowedPair .uint8 "lean_string_dec_eq"
  verify official `String.hash #[(.object, true)] .uint64 "lean_string_hash"
  if owner == `OmegaInit.Data.String.Basic then
    for n in [`String.toList, `String.data] do
      verify official n #[(.object, false)] .tobject "lean_string_data"
    verify official `String.decidableLT borrowedPair .uint8 "lean_string_dec_lt"
  searchPathRef.set [lib]
  let read := importModules #[{module := owner, importAll := true : Import}] {}
  let mut env ← read
  let names := if owner == `OmegaInit.Prelude then
    [(`Omega.String.ofList, "omega_string_of_list"), (`Omega.Char.ofNat, "omega_char_of_nat"),
     (`Omega.String.utf8ByteSize, "omega_string_byte_size"), (`Omega.String.toByteArray, "omega_string_to_bytes"),
     (`Omega.String.decEq, "omega_string_dec_eq"), (`Omega.String.hash, "omega_string_hash")]
  else [(`Omega.String.toList, "omega_string_to_list"), (`Omega.String.data, "omega_string_data"),
        (`Omega.String.decidableLT, "omega_string_dec_lt")]
  let names := names.filter fun (n, _) => (env.find? n).any (· matches .defnInfo _ | .opaqueInfo _) &&
    (getSigCore? env impureSigExt n).isNone
  if names.isEmpty then return
  for n in [`Nat, `Omega.List, `Omega.Fin, `Omega.BitVec, `Omega.UInt8, `Omega.UInt32, `Omega.UInt64, `Decidable, `Bool,
            `Omega.Char, `Omega.Array, `Omega.ByteArray, `Omega.String] do
    unless (monoTypeExt.find? env n).isSome do
      let some idx := env.getModuleIdxFor? n | throw <| IO.userError s!"missing literal type {n}"
      writeCode lib env.header.moduleNames[idx]! (← compileLayouts env n) layouts
      env ← read
  checkNativeNat env
  for n in [`Decidable, `Omega.Fin, `Omega.BitVec, `Omega.UInt8, `Omega.UInt32, `Omega.UInt64, `Omega.Char,
            `Omega.Array, `Omega.ByteArray, `Omega.String] do
    let some (some field) := impureTrivialStructureInfoExt.find? env n
      | throw <| IO.userError s!"missing literal representation of {n}"
    unless field.fieldIdx == 0 do throw <| IO.userError s!"unexpected representation of {n}"
  let some cons := ctorLayoutExt.find? env `Omega.List.cons | throw <| IO.userError "missing list layout"
  let #[.object 0 _, .object 1 _] := cons.fieldInfo | throw <| IO.userError "incorrect character-list fields"
  unless cons.ctorInfo.cidx == 1 && cons.ctorInfo.size == 2 do throw <| IO.userError "incorrect list tag or size"
  for (name, tag) in [(`Bool.false, 0), (`Bool.true, 1)] do
    let some ctor := ctorLayoutExt.find? env name | throw <| IO.userError s!"missing constructor {name}"
    unless ctor.ctorInfo.cidx == tag && ctor.ctorInfo.size == 0 && ctor.ctorInfo.ssize == 0 do
      throw <| IO.userError s!"unexpected decision representation for {name}"
  let context ← localEnv env owner (names.map Prod.fst).toArray
  let compiled ← compile context do
    for (n, symbol) in names do
      let kind : ConstantKind := if (env.find? n).any (· matches .opaqueInfo _) then .opaque else .defn
      modifyEnv fun e => privateConstKindsExt.insert e n kind
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all symbol]⟩)
      (← compileDeclsRef.get) #[n] {}
  for (n, symbol) in names do
    if n == `Omega.String.decEq || n == `Omega.String.decidableLT then
      verify compiled n #[(.tobject, true), (.tobject, true)] .uint8 symbol
    else
      let borrow := n == `Omega.String.utf8ByteSize || n == `Omega.String.hash
      verify compiled n #[(.tobject, borrow)] .tobject symbol
  writeCode lib owner compiled (codeExtensions ++ #[privateConstKindsExt.name])
  let source := if owner == `OmegaInit.Prelude then "literal_runtime.c" else "string_list_runtime.c"
  emitBridge compiled owner (System.FilePath.mk "src/OmegaChecks/InitPort" / source) out

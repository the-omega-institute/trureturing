module
import all Lean.Environment
import all Lean.OriginalConstKind
import Lean.Compiler.LCNF.PhaseExt
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.Compiler.LCNF.MonoTypes
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState

open Lean Compiler.LCNF OmegaChecks.InitPort.NativeState

/-- Raw positions erase to the same checked natural that the physical String ABI expects. -/
private def positionOps : List (Name × String × String × IR.IRType × IR.IRType) :=
  let cursor := fun (stem : Name) (strict upstream : String) (sourceResult strictResult : IR.IRType) =>
    [(`String.Pos.Raw ++ stem, strict, upstream, sourceResult, strictResult), (`String ++ stem, strict, upstream, sourceResult, strictResult)]
  cursor `get "omega_string_get_char" "lean_string_utf8_get" .uint32 .tobject ++
  cursor `next "omega_string_next" "lean_string_utf8_next" .tobject .tobject ++
  cursor `prev "omega_string_prev" "lean_string_utf8_prev" .tobject .tobject ++
  cursor `atEnd "omega_string_at_end" "lean_string_utf8_at_end" .uint8 .uint8 ++
  [(`String.Pos.Raw.isValid, "omega_string_valid_pos", "lean_string_is_valid_pos", .uint8, .uint8)]

private structure TextOp where
  name : Name
  symbol : String
  pinned : String
  args : Array (IR.IRType × Bool)
  result : IR.IRType

private def textOps (owner : Name) : List TextOp :=
  let appendArgs := #[(IR.IRType.object, false), (.object, true)]
  match owner with
  | `OmegaInit.Data.String.Bootstrap => [
    ⟨`String.push, "omega_string_push", "lean_string_push", #[(.object, false), (.uint32, false)], .object⟩,
    ⟨`String.Internal.length, "omega_string_length", "lean_string_length", #[(.object, true)], .tobject⟩,
    ⟨`String.Internal.append, "omega_string_append", "lean_string_append", appendArgs, .object⟩,
    ⟨`String.Internal.extract, "omega_string_extract", "lean_string_utf8_extract",
      #[(.object, true), (.tobject, true), (.tobject, true)], .object⟩,
    ⟨`String.mk, "omega_string_of_list", "lean_string_mk", #[(.tobject, false)], .object⟩]
  | `OmegaInit.Data.String.Defs => [
    ⟨`String.append, "omega_string_append", "lean_string_append", appendArgs, .object⟩,
    ⟨`String.toUTF8, "omega_string_utf8", "lean_string_to_utf8", #[(.object, true)], .object⟩,
    ⟨`String.markLinear, "omega_string_mark", "lean_string_mark_linear", #[(.object, false)], .object⟩,
    ⟨`String.propagateMark, "omega_string_propagate", "lean_string_propagate_mark",
      #[(.object, true), (.object, false)], .object⟩]
  | _ => []

public unsafe def main (args : List String) : IO Unit := do
  let [lib, out, ownerArg] := args | throw <| IO.userError "expected strict library, native output and module"
  let owner := ownerArg.toName
  let extra := textOps owner
  unless owner == `OmegaInit.Prelude || owner == `OmegaInit.Data.String.Basic || !extra.isEmpty do
    throw <| IO.userError s!"unsupported string owner {owner}"
  let official ← importModules #[{module := owner.replacePrefix `OmegaInit `Init, importAll := true}] {}
  verify official `panicCore #[(.erased, false), (.tobject, true), (.object, false)] .tobject "lean_panic_fn_borrowed"
  verify official `Array.get!Internal #[(.erased, false), (.tobject, true), (.object, true), (.tobject, true)] .tobject "lean_array_get"
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
    verify official `ByteArray.validateUTF8 #[(.object, true)] .uint8 "lean_string_validate_utf8"
    for (name, _, symbol, sourceResult, _) in positionOps do
      verify official name #[(.object, true), (.tobject, true)] sourceResult symbol
  for op in extra do verify official op.name op.args op.result op.pinned
  searchPathRef.set [lib]
  let read := importModules #[{module := owner, importAll := true : Import}] {}
  let mut env ← read
  let names := if !extra.isEmpty then extra.map fun op => (`Omega ++ op.name, op.symbol)
  else if owner == `OmegaInit.Prelude then
    [(`Omega.String.ofByteArray, "omega_string_of_bytes"), (`Omega.panicCore, "omega_panic_core"), (`Omega.Array.get!Internal, "omega_array_get_bang"),
     (`Omega.String.ofList, "omega_string_of_list"), (`Omega.Char.ofNat, "omega_char_of_nat"),
     (`Omega.String.utf8ByteSize, "omega_string_byte_size"), (`Omega.String.toByteArray, "omega_string_to_bytes"),
     (`Omega.String.decEq, "omega_string_dec_eq"), (`Omega.String.hash, "omega_string_hash")]
  else [(`Omega.String.toList, "omega_string_to_list"), (`Omega.String.data, "omega_string_data"),
        (`Omega.String.decidableLT, "omega_string_dec_lt"), (`Omega.ByteArray.validateUTF8, "omega_bytes_valid_utf8")] ++
       positionOps.map fun (n, symbol, _, _, _) => (`Omega ++ n, symbol)
  let names := names.filter fun (n, _) => (env.find? n).any (· matches .defnInfo _ | .opaqueInfo _ | .ctorInfo _) &&
    (getSigCore? env impureSigExt n).isNone
  if names.isEmpty then return
  for n in [`Nat, `Omega.Inhabited, `Omega.List, `Omega.Fin, `Omega.BitVec, `Omega.UInt8, `Omega.UInt32, `Omega.UInt64, `Decidable, `Bool, `Omega.String.Pos.Raw,
            `Omega.Char, `Omega.Array, `Omega.ByteArray, `Omega.String] do
    if !env.contains n then continue
    unless (monoTypeExt.find? env n).isSome do
      let some idx := env.getModuleIdxFor? n | throw <| IO.userError s!"missing literal type {n}"
      writeCode lib env.header.moduleNames[idx]! (← compileLayouts env n) layouts
      env ← read
  if env.contains `Omega.String then checkStrictString env
  else if env.contains `Omega.ByteArray then checkStrictBytes env
  else checkNativeNat env
  for n in [`Omega.Inhabited, `Decidable, `Omega.String.Pos.Raw, `Omega.UInt32, `Omega.UInt64, `Omega.Char] do
    if env.contains n then checkErasedField env n
  if env.contains `Bool then
    for (name, tag) in [(`Bool.false, 0), (`Bool.true, 1)] do
      let some ctor := ctorLayoutExt.find? env name | throw <| IO.userError s!"missing constructor {name}"
      unless ctor.ctorInfo.cidx == tag && ctor.ctorInfo.size == 0 && ctor.ctorInfo.ssize == 0 do
        throw <| IO.userError s!"unexpected decision representation for {name}"
  let context ← localEnv env owner (names.map Prod.fst).toArray
  let compiled ← compile context do
    for (n, symbol) in names do
      let kind : ConstantKind := if (env.find? n).any (· matches .opaqueInfo _) then .opaque else .defn
      unless n == `Omega.String.ofByteArray do modifyEnv fun e => privateConstKindsExt.insert e n kind
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all symbol]⟩)
      (← compileDeclsRef.get) #[n] {}
  for (n, symbol) in names do
    if let some op := extra.find? (fun op => n == `Omega ++ op.name) then
      verify compiled n (op.args.map fun (_, borrow) => (.tobject, borrow)) .tobject symbol
    else if n == `Omega.String.ofByteArray then
      verify official `String.ofByteArray #[(.object, false), (.erased, false)] .object "lean_string_from_utf8_unchecked"
      verify compiled n #[(.tobject, false), (.erased, false)] .tobject symbol
    else if n == `Omega.panicCore then
      verify compiled n #[(.erased, false), (.tobject, true), (.tobject, false)] .tobject symbol
    else if n == `Omega.Array.get!Internal then
      verify compiled n #[(.erased, false), (.tobject, true), (.tobject, true), (.tobject, true)] .tobject symbol
    else if let some (_, _, _, _, strictResult) := positionOps.find? (fun (name, _, _, _, _) => n == `Omega ++ name) then
      verify compiled n #[(.tobject, true), (.tobject, true)] strictResult symbol
    else if n == `Omega.ByteArray.validateUTF8 then
      verify compiled n #[(.tobject, true)] .uint8 symbol
    else if n == `Omega.String.decEq || n == `Omega.String.decidableLT then
      verify compiled n #[(.tobject, true), (.tobject, true)] .uint8 symbol
    else
      let borrow := n == `Omega.String.utf8ByteSize || n == `Omega.String.hash
      verify compiled n #[(.tobject, borrow)] .tobject symbol
  writeCode lib owner compiled (codeExtensions ++ #[privateConstKindsExt.name])
  let source : String := match owner with
    | `OmegaInit.Prelude => "literal_runtime.c"
    | `OmegaInit.Data.String.Bootstrap => "string_bootstrap_runtime.c"
    | `OmegaInit.Data.String.Defs => "string_defs_runtime.c"
    | _ => "string_list_runtime.c"
  emitBridge compiled owner (some (System.FilePath.mk "src/OmegaChecks/InitPort" / System.FilePath.mk source)) out

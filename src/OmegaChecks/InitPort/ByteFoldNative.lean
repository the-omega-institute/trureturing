module
public import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.IndexedNative
import OmegaChecks.InitPort.Translation
import Lean.Compiler.ImplementedByAttr

open Lean
namespace OmegaChecks.InitPort.ByteFoldNative

public def supported (n : Name) : Bool := [`ByteArray.foldlM, `ByteArray.foldlM.loop, `ByteArray.forIn, `ByteArray.forIn.loop].contains n

private def obj (t : IR.IRType) := t == .tobject || t == .object

/-- A polymorphic accumulator and its monad dictionary retain their boxed calling convention.
Convert the packed input once and pass the same strict effectful callback to the pinned fold. -/
public def wrapper (source strict : Environment) (n : Name) (symbol : String) : IO String := do
  let official := n.replacePrefix `Omega .anonymous
  let some info := source.find? official | throw <| IO.userError s!"missing pinned byte fold {official}"
  let some target := strict.find? n | throw <| IO.userError s!"missing strict byte fold {n}"
  unless target.type == InitKernelPort.translate InitKernelPort.portName info.type do throw <| IO.userError s!"strict byte fold type mismatch: {n}"
  let replacement := if official == `ByteArray.foldlM then some `ByteArray.foldlMUnsafe
    else if official == `ByteArray.forIn then some `ByteArray.forInUnsafe else none
  let compiled ← match replacement with
    | none => pure official
    | some fast => do
      unless Compiler.getImplementedBy? source official == some fast do throw <| IO.userError s!"incorrect byte fold override: {official}"
      let some f := source.find? fast | throw <| IO.userError s!"missing byte fold override: {fast}"
      unless f.type == info.type do throw <| IO.userError s!"byte fold override signature differs: {fast}"
      pure fast
  let some (.fdecl _ args .tobject ..) := IR.findEnvDecl source compiled | throw <| IO.userError s!"missing pinned byte fold IR: {compiled}"
  let some (.extern _ actual .tobject ⟨[.standard `all actualSymbol]⟩) := IR.findEnvDecl strict n | throw <| IO.userError s!"missing compiled byte fold: {n}"
  unless args.size == actual.size && actualSymbol == symbol do throw <| IO.userError s!"invalid strict byte fold arity: {n}"
  NativeState.checkStrictBytes strict
  IndexedNative.checkDataTypes source strict [`Monad, `Applicative, `Pure, `Functor, `Seq, `SeqLeft, `SeqRight, `Bind, `ForInStep]
  let mut type := info.type
  let mut operands := #[]
  let mut decls := #[]
  let mut prepare := ""
  let mut cleanup := ""
  let mut converted := false
  for (a,b) in args.zip actual, i in [:args.size] do
    let .forallE _ domain body _ := type | throw <| IO.userError s!"missing byte fold argument {n} {i}"
    type := body
    if a.ty == .erased && b.ty == .erased then
      operands := operands.push "lean_box(0)"
      continue
    unless obj a.ty && obj b.ty do throw <| IO.userError s!"invalid byte fold argument {n} {i}: {a.ty}/{b.ty}"
    let x := "a" ++ toString i
    decls := decls.push ("lean_object *" ++ x)
    if domain.consumeMData.isConstOf `ByteArray then
      unless !converted && a.ty == .object && b.ty == .tobject do throw <| IO.userError "unexpected byte array layout in fold"
      converted := true
      prepare := prepare ++ s!"  lean_object *bytes = omega_bytes_to_lean({x});\n"
      operands := operands.push "bytes"
      if a.borrow then cleanup := cleanup ++ "  lean_dec(bytes);\n"
      unless b.borrow do cleanup := cleanup ++ s!"  lean_dec({x});\n"
    else
      operands := operands.push x
      if b.borrow && !a.borrow then prepare := prepare ++ s!"  lean_inc({x});\n"
      if !b.borrow && a.borrow then cleanup := cleanup ++ s!"  lean_dec({x});\n"
  unless converted do throw <| IO.userError s!"missing byte array operand at {n}"
  let entry := getSymbolStem source compiled
  let proto := String.intercalate ", " (args.toList.map (fun _ => "lean_object *"))
  let call := s!"{entry}({String.intercalate ", " operands.toList})"
  return s!"\n#include \"strict_byte_array.h\"\nextern lean_obj_res {entry}({proto});\nLEAN_EXPORT lean_obj_res {symbol}({String.intercalate ", " decls.toList}) \{\n" ++
    s!"{prepare}  lean_obj_res result = {call};\n{cleanup}  return result;\n}\n"

end OmegaChecks.InitPort.ByteFoldNative

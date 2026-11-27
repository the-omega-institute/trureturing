module
public import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.Translation
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF
namespace OmegaChecks.InitPort.IndexedNative

/-- These eliminators pass arbitrary motive values through without inspecting them.
Indices and captured callback arguments use the strict kernel Nat and the erased Fin wrapper. -/
public def supported (n : Name) : Bool :=
  [`Fin.cases, `Fin.induction, `Fin.induction.go, `Fin.inductionOn, `Fin.reverseInduction,
   `Fin.reverseInduction.go, `Fin.lastCases, `Fin.succRec, `Fin.succRecOn,
   `Nat.recAux, `Nat.recCompiled, `Nat.repeat, `Nat.repeatTR, `Nat.div.inductionOn, `Nat.mod.inductionOn].contains n

private def objectType (t : IR.IRType) := t == .tobject || t == .object || t == .tagged

public def wrapper (source strict : Environment) (n : Name) (symbol : String) : IO String := do
  let official := n.replacePrefix `Omega .anonymous
  let some ci := source.find? official | throw <| IO.userError s!"missing pinned indexed eliminator {official}"
  let some target := strict.find? n | throw <| IO.userError s!"missing strict indexed eliminator {n}"
  unless target.type == InitKernelPort.translate InitKernelPort.portName ci.type do
    throw <| IO.userError s!"indexed eliminator type mismatch: {n}"
  if official.getRoot == `Fin then
    let some (some field) := impureTrivialStructureInfoExt.find? strict `Omega.Fin | throw <| IO.userError "missing strict Fin layout"
    unless field.fieldIdx == 0 do throw <| IO.userError "unexpected strict Fin value slot"
  let some (.fdecl _ args ret ..) := IR.findEnvDecl source official | throw <| IO.userError s!"missing pinned native eliminator {official}"
  let some (.extern _ actual out ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n | throw <| IO.userError s!"missing generated eliminator {n}"
  unless objectType ret && objectType out && args.size == actual.size && entry == symbol do
    throw <| IO.userError s!"incompatible indexed eliminator ABI: {n}"
  let mut operands := #[]
  let mut decls := #[]
  let mut prepare := ""
  let mut cleanup := ""
  for (a, b) in args.zip actual, i in [:args.size] do
    if a.ty == .erased && b.ty == .erased then
      -- The ordinary pinned C function retains the erased argument. The strict extern omits it.
      operands := operands.push "lean_box(0)"
    else if objectType a.ty && objectType b.ty then
      let x := "a" ++ toString i
      operands := operands.push x
      decls := decls.push ("lean_object *" ++ x)
      if b.borrow && !a.borrow then prepare := prepare ++ s!"  lean_inc({x});\n"
      if !b.borrow && a.borrow then cleanup := cleanup ++ s!"  lean_dec({x});\n"
    else throw <| IO.userError s!"incompatible eliminator argument at {n} {i}: {a.ty}/{b.ty}"
  let cfg := (getExportNameFor? source official).map (·.toString)
  let entry := cfg.getD (getSymbolStem source official)
  let proto := String.intercalate ", " (args.toList.map (fun _ => "lean_object *"))
  let call := s!"{entry}({String.intercalate ", " operands.toList})"
  return s!"\nextern lean_obj_res {entry}({proto});\nLEAN_EXPORT lean_obj_res {symbol}({String.intercalate ", " decls.toList}) \{\n" ++
    s!"{prepare}  lean_obj_res r = {call};\n{cleanup}  return r;\n}\n"

end OmegaChecks.InitPort.IndexedNative

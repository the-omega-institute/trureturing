module
public import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.Translation
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF
namespace OmegaChecks.InitPort.IndexedNative

/-- These eliminators pass arbitrary motive values through without inspecting them.
Indices and captured callback arguments use the strict kernel Nat and the erased Fin wrapper. -/
private def linear (n : Name) : Bool :=
  let p := `Nat.Internal.Linear
  [`Expr.toPoly.go, `Poly.insert, `Poly.cancelAux, `Poly.norm.go, `Poly.isNum?, `Poly.isZero, `Poly.isNonZero, `instBEqExpr.beq,
   `Poly.toExpr.go].any fun suffix => n == p ++ suffix

private def quotientEliminator (n : Name) : Bool :=
  [`Quot.hrecOn, `Quotient.hrecOn, `Quotient.lift, `Quotient.liftOn, `Quotient.liftOn₂,
   `Quotient.lift₂, `Squash.lift].contains n

private def listTraversal (n : Name) : Bool :=
  [`List.filterMapTR, `List.flatMapTR, `List.flattenTR, `List.intercalateTR, `List.reduceOption].contains n

public def supported (n : Name) : Bool :=
  linear n || quotientEliminator n || listTraversal n || n == `List.mapMonoM ||
  [`Acc.recC, `Acc.ndrecC, `Acc.ndrecOnC, `WellFounded.fixFC,
   `Lean.Grind.CommRing.Mon.revlexWF, `Lean.Grind.CommRing.Mon.revlexFuel, `Lean.Grind.CommRing.Mon.revlex,
   `Lean.Grind.CommRing.Mon.grevlex, `Lean.Grind.CommRing.Power.revlex,
   `Lean.RArray.getImpl, `Fin.cases, `Fin.induction, `Fin.induction.go, `Fin.inductionOn, `Fin.reverseInduction,
   `Fin.reverseInduction.go, `Fin.lastCases, `Fin.succRec, `Fin.succRecOn,
   `Nat.fold, `Nat.foldTR, `Nat.foldRev, `Nat.dfold, `Nat.dfoldRev, `Nat.any, `Nat.anyTR, `Nat.all, `Nat.allTR,
   `Prod.foldI, `Prod.anyI, `Prod.allI,
   `Nat.recAux, `Nat.recCompiled, `Nat.repeat, `Nat.repeatTR, `Nat.div.inductionOn, `Nat.mod.inductionOn,
   `Nat.decidableBallLTTR, `Nat.decidableExistsLE, `Nat.decidableExistsLTTR, `Nat.decidableBallLE,
   `Nat.decidableExistsLT'TR, `Nat.allLTTR, `Nat.decidableExistsFin, `Nat.decidableForallFin,
   `Nat.anyLTTR, `Nat.decidableExistsLE'].contains n

private def objectType (t : IR.IRType) := t == .tobject || t == .object || t == .tagged

private def sameField : CtorFieldInfo → CtorFieldInfo → Bool
  | .object i t, .object j u | .scalar 1 i t, .scalar 1 j u => i == j && t == u
  | .erased, .erased | .void, .void => true
  | _, _ => false

/-- Compare every constructor field and its native offset before sharing a runtime representation. -/
public def checkDataTypes (source strict : Environment) (types : List Name) : IO Unit := do
  for name in types do
    let some (.inductInfo s) := source.find? name | throw <| IO.userError s!"missing pinned data type {name}"
    let some (.inductInfo t) := strict.find? (InitKernelPort.portName name) | throw <| IO.userError s!"missing strict data type {name}"
    unless s.ctors.map InitKernelPort.portName == t.ctors do throw <| IO.userError s!"different constructors of {name}"
    for (a,b) in s.ctors.zip t.ctors do
      let some ca := source.find? a | throw <| IO.userError s!"missing {a}"
      let some cb := strict.find? b | throw <| IO.userError s!"missing {b}"
      unless cb.type == InitKernelPort.translate InitKernelPort.portName ca.type do throw <| IO.userError s!"different constructor fields in {b}"
      let some x := ctorLayoutExt.find? source a | throw <| IO.userError s!"missing layout for {a}"
      let some y := ctorLayoutExt.find? strict b | throw <| IO.userError s!"missing layout for {b}"
      let l := x.ctorInfo
      let r := y.ctorInfo
      unless l.cidx == r.cidx && l.size == r.size && l.usize == r.usize && l.ssize == r.ssize &&
          x.fieldInfo.size == y.fieldInfo.size && (x.fieldInfo.zip y.fieldInfo).all (fun (f,g) => sameField f g) do
        throw <| IO.userError s!"different native layout for {a} and {b}"

public def wrapper (source strict : Environment) (n : Name) (symbol : String) : IO String := do
  let official := n.replacePrefix `Omega .anonymous
  let some ci := source.find? official | throw <| IO.userError s!"missing pinned indexed eliminator {official}"
  let some target := strict.find? n | throw <| IO.userError s!"missing strict indexed eliminator {n}"
  unless target.type == InitKernelPort.translate InitKernelPort.portName ci.type do
    throw <| IO.userError s!"indexed eliminator type mismatch: {n}"
  if linear official then checkDataTypes source strict [`Prod, `Option, `List, `Nat.Internal.Linear.Expr]
  if listTraversal official then checkDataTypes source strict [`List, `Option]
  if official.getPrefix == `Lean.Grind.CommRing.Mon || official == `Lean.Grind.CommRing.Power.revlex then
    checkDataTypes source strict [`Lean.Grind.CommRing.Mon, `Lean.Grind.CommRing.Power, `Ordering]
  if official == `Lean.RArray.getImpl then checkDataTypes source strict [`Lean.RArray]
  if official.getRoot == `Prod then checkDataTypes source strict [`Prod]
  if official.getRoot == `Fin then
    let some (some field) := impureTrivialStructureInfoExt.find? strict `Omega.Fin | throw <| IO.userError "missing strict Fin layout"
    unless field.fieldIdx == 0 do throw <| IO.userError "unexpected strict Fin value slot"
  let impl ← if official == `List.mapMonoM then do
    let impl := mkPrivateNameCore `Init.Data.List.BasicAux `List.mapMonoMImp
    let some info := source.find? impl | throw <| IO.userError "missing pinned sharing-preserving list traversal"
    unless (Compiler.getImplementedBy? source official) == some impl && info.type == ci.type do
      throw <| IO.userError "unexpected sharing-preserving list implementation"
    checkDataTypes source strict [`List, `Monad, `Applicative, `Pure, `Functor, `Seq, `SeqLeft, `SeqRight, `Bind]
    pure impl
  else pure official
  let some (.fdecl _ args ret ..) := IR.findEnvDecl source impl | throw <| IO.userError s!"missing pinned native eliminator {official}"
  let some (.extern _ actual out ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n | throw <| IO.userError s!"missing generated eliminator {n}"
  let result ← if objectType ret && objectType out then pure "lean_obj_res"
    else if ret == .uint8 && out == .uint8 then pure "uint8_t"
    else throw <| IO.userError s!"different indexed result representation: {n}"
  unless args.size == actual.size && entry == symbol do
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
  let cfg := (getExportNameFor? source impl).map (·.toString)
  let entry := cfg.getD (getSymbolStem source impl)
  let proto := String.intercalate ", " (args.toList.map (fun _ => "lean_object *"))
  let call := s!"{entry}({String.intercalate ", " operands.toList})"
  return s!"\nextern {result} {entry}({proto});\nLEAN_EXPORT {result} {symbol}({String.intercalate ", " decls.toList}) \{\n" ++
    s!"{prepare}  {result} r = {call};\n{cleanup}  return r;\n}\n"

end OmegaChecks.InitPort.IndexedNative

module
public import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.UnsafeRuntime
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF
namespace OmegaChecks.InitPort.IndexedNative

/-- These eliminators pass arbitrary motive values through without inspecting them.
Indices and captured callback arguments use the strict kernel Nat and the erased Fin wrapper. -/
private def linear (n : Name) : Bool :=
  let p := `Nat.Internal.Linear
  [`Expr.toPoly.go, `Poly.insert, `Poly.cancelAux, `Poly.norm.go, `Poly.isNum?, `Poly.isZero, `Poly.isNonZero, `instBEqExpr.beq,
   `Poly.toExpr.go].any fun suffix => n == p ++ suffix

private def attachment (n : Name) : Bool :=
  [`List.attachWith, `Array.attachWith, `Option.attachWith, `Vector.attachWith].contains n

private def envelopeLift (n : Name) : Bool :=
  [`Lean.Grind.Ring.OfSemiring.Q.liftOn₂, `Lean.Grind.IntModule.OfNatModule.Q.liftOn₂].contains n

private def quotientEliminator (n : Name) : Bool :=
  [`Quot.hrecOn, `Quotient.hrecOn, `Quotient.lift, `Quotient.liftOn, `Quotient.liftOn₂,
   `Quotient.lift₂, `Squash.lift].contains n

private def listTraversal (n : Name) : Bool :=
  [`List.filterMapTR, `List.flatMapTR, `List.flattenTR, `List.intercalateTR, `List.reduceOption].contains n

public def supported (n : Name) : Bool :=
  envelopeLift n || attachment n || linear n || quotientEliminator n || listTraversal n ||
  [`withPtrEq, `ShareCommon.shareCommon', `Array.mapMono, `List.mapMonoM, `List.flatMapMTR.loop, `List.splitOn, `List.splitOnPTR, `BitVec.flattenListFast].contains n ||
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

/-- The guarded equality fast path compares the original borrowed objects in operand order. -/
private def pointerComparison (body : IR.FnBody) (left right : IR.VarId) : Option (IR.VarId × IR.FnBody) := do
  let .vdecl a .usize (.fap `ptrAddrUnsafe #[.erased, .var x]) body := body | none
  let .vdecl b .usize (.fap `ptrAddrUnsafe #[.erased, .var y]) body := body | none
  let .vdecl result .uint8 (.fap `USize.decEq #[.var v, .var w]) rest := body | none
  guard (x == left && y == right && a == v && b == w)
  return (result, rest)

private def checkGuardedPointerEq (env : Environment) : Bool := Id.run do
  let some observer := env.find? `ptrAddrUnsafe | return false
  unless UnsafeRuntime.isAddress observer false do return false
  let some (.defnInfo eq) := env.find? `ptrEq | return false
  let some (.defnInfo guarded) := env.find? `withPtrEqUnsafe | return false
  unless PointerComparison.isOriginal (.defnInfo eq) false && PointerComparison.isOriginal (.defnInfo guarded) false do return false
  let some (.fdecl _ cmpArgs .uint8 cmpBody _) := IR.findEnvDecl env eq.name | return false
  let some (.fdecl _ guardArgs .uint8 guardBody _) := IR.findEnvDecl env guarded.name | return false
  let operands := #[(IR.IRType.erased, false), (.tobject, true), (.tobject, true)]
  unless cmpArgs.map (fun a => (a.ty, a.borrow)) == operands &&
      guardArgs.map (fun a => (a.ty, a.borrow)) == operands ++ #[(.object, false), (.erased, false)] do return false
  let some (cmp, .ret (.var result)) := pointerComparison cmpBody cmpArgs[1]!.x cmpArgs[2]!.x | return false
  let some (test, .case `UInt8 branch .uint8 #[.ctor onFalse fallback, .ctor onTrue success]) :=
    pointerComparison guardBody guardArgs[1]!.x guardArgs[2]!.x | return false
  let .vdecl unit .tagged (.ctor unitCtor #[]) (.vdecl applied .tagged (.ap k #[.var argument])
    (.vdecl unboxed .uint8 (.unbox boxed) (.ret (.var output)))) := fallback | return false
  let .dec released 1 _ false (.ret (.var yes)) := success | return false
  return onFalse == ⟨`Bool.false, 0, 0, 0, 0⟩ && onTrue == ⟨`Bool.true, 1, 0, 0, 0⟩ &&
    unitCtor == ⟨`PUnit.unit, 0, 0, 0, 0⟩ && cmp == result && test == branch &&
    unit == argument && k == guardArgs[3]!.x && applied == boxed && unboxed == output &&
    released == k && yes == test

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

/-- Verify the runtime fields shared by native traversals that replace the monadic pure. -/
public def checkMonadDictionary (source strict : Environment) : IO Unit := do
  checkDataTypes source strict [`Monad, `Applicative, `Pure, `Functor, `Seq, `SeqLeft, `SeqRight, `Bind]
  for (ctor, names) in [(`Monad.mk, [`toApplicative, `toBind]), (`Applicative.mk, [`toFunctor, `toPure, `toSeq, `toSeqLeft, `toSeqRight])] do
    let some layout := ctorLayoutExt.find? source ctor | throw <| IO.userError s!"missing monad dictionary {ctor}"
    unless layout.ctorInfo.size == names.length && layout.ctorInfo.cidx == 0 && layout.ctorInfo.ssize == 0 &&
        layout.ctorInfo.usize == 0 do throw <| IO.userError s!"unexpected monad dictionary {ctor}"
    for field in names, i in [:names.length] do
      let some projection := source.getProjectionFnInfo? (ctor.getPrefix ++ field)
        | throw <| IO.userError s!"missing monad projection {field}"
      let .object j _ := layout.fieldInfo[i]! | throw <| IO.userError "monad dictionary field is unboxed"
      unless projection.i == i && j == i do throw <| IO.userError s!"reordered monad dictionary field {field}"

/-- After erasing the subtype proof, attaching it retains the original container. -/
private def attachmentWrapper (source strict : Environment) (official n : Name) (symbol : String) : IO String := do
  let owner := `Init.Data ++ official.getPrefix ++ `Attach
  let impl := mkPrivateNameCore owner (official.appendAfter "Impl")
  let some (.defnInfo code) := source.find? impl | throw <| IO.userError s!"missing pinned attachment {impl}"
  unless (Compiler.getImplementedBy? source official) == some impl && code.safety == .unsafe do
    throw <| IO.userError s!"unexpected attachment implementation {official}"
  let some (.fdecl _ pinned result (.inc kept 1 _ false (.ret (.var returned))) _) := IR.findEnvDecl source impl
    | throw <| IO.userError s!"attachment does not retain its input {impl}"
  let vector := official == `Vector.attachWith
  let index := if vector then 2 else 1
  let importedType : IR.IRType := if vector || official == `Array.attachWith then .object else .tobject
  let signature : Array IR.IRType := #[.erased] ++ (if vector then #[.tobject] else #[]) ++ #[importedType, .erased, .erased]
  unless pinned.map (·.ty) == signature && result == importedType && pinned[index]!.borrow &&
      kept == pinned[index]!.x && kept == returned do throw <| IO.userError s!"wrong native attachment input {impl}"
  let some (some tag) := impureTrivialStructureInfoExt.find? strict `Omega.Subtype
    | throw <| IO.userError "strict subtype proof occupies a runtime field"
  let some (.extern _ args .tobject ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n
    | throw <| IO.userError s!"missing strict attachment signature {n}"
  unless entry == symbol && tag.fieldIdx == 0 && args.map (·.ty) == signature.set! index .tobject do
    throw <| IO.userError s!"unexpected strict attachment layout {n}"
  let length := if vector then "lean_obj_arg length, " else ""
  let release := if vector && !args[1]!.borrow then "lean_dec(length); " else ""
  let retain := if args[index]!.borrow then "lean_inc(xs); " else ""
  return s!"\nLEAN_EXPORT lean_obj_res {entry}({length}lean_obj_arg xs) \{ {release}{retain}return xs; }\n"

public def wrapper (source strict : Environment) (n : Name) (symbol : String) : IO String := do
  let official := n.replacePrefix `Omega .anonymous
  let some ci := source.find? official | throw <| IO.userError s!"missing pinned indexed eliminator {official}"
  let some target := strict.find? n | throw <| IO.userError s!"missing strict indexed eliminator {n}"
  unless target.type == InitKernelPort.translate InitKernelPort.portName ci.type do
    throw <| IO.userError s!"indexed eliminator type mismatch: {n}"
  if envelopeLift official then
    let some (.fdecl _ args .tobject (.vdecl result .tobject (.ap callback #[.var x, .var y]) (.ret (.var returned))) _) :=
        IR.findEnvDecl source official | throw <| IO.userError s!"unexpected envelope quotient lift {official}"
    unless args.size == 7 && args[3]!.x == x && args[4]!.x == y && args[5]!.x == callback && returned == result do
      throw <| IO.userError s!"envelope quotient lift changed its representative arguments {official}"
    checkDataTypes source strict [`Prod]
  if official == `Array.mapMono then
    let some (.fdecl _ args .object ..) := IR.findEnvDecl source official
      | throw <| IO.userError "missing pinned array map"
    let some (.extern _ actual .tobject ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n
      | throw <| IO.userError "missing strict array map"
    let some (some field) := impureTrivialStructureInfoExt.find? strict `Omega.Array
      | throw <| IO.userError "strict array map requires the list field"
    checkDataTypes source strict [`List]
    unless Compiler.getImplementedBy? source `Array.mapMonoM ==
        some (mkPrivateNameCore `Init.Data.Array.BasicAux `mapMonoMImp) && field.fieldIdx == 0 &&
        args.map (·.ty) == #[.erased, .object, .tobject] && args.all (!·.borrow) &&
        actual.map (·.ty) == #[.erased, .tobject, .tobject] && entry == symbol do
      throw <| IO.userError s!"unexpected monomorphic array map {actual.map fun p => (p.ty, p.borrow)}"
    let keepXs := if actual[1]!.borrow then "lean_inc(xs); " else ""
    let keepF := if actual[2]!.borrow then "lean_inc(f); " else ""
    return s!"\n#include \"strict_array_set.h\"\nLEAN_EXPORT lean_obj_res {entry}(lean_obj_arg xs, lean_obj_arg f) \{ {keepXs}{keepF}return omega_array_list_map_mono(xs, f); }\n"
  if official == `ShareCommon.shareCommon' then
    let some (.extern _ pinned .tobject ⟨[.standard `all "lean_sharecommon_quick"]⟩) := IR.findEnvDecl source official
      | throw <| IO.userError "missing pinned object-sharing primitive"
    let some (.extern _ actual .tobject ⟨[.standard `all entry]⟩) := IR.findEnvDecl strict n
      | throw <| IO.userError "missing strict object-sharing primitive"
    unless entry == symbol && pinned.map (fun p => (p.ty, p.borrow)) == #[(.erased, false), (.tobject, true)] &&
        actual.map (·.ty) == pinned.map (·.ty) do throw <| IO.userError "unexpected object-sharing signature"
    let release := if actual[1]!.borrow then "" else "lean_dec(x); "
    return s!"\nextern lean_obj_res lean_sharecommon_quick(b_lean_obj_arg);\nLEAN_EXPORT lean_obj_res {entry}(lean_obj_arg x) \{ lean_obj_res r = lean_sharecommon_quick(x); {release}return r; }\n"
  if attachment official then return ← attachmentWrapper source strict official n symbol
  if [`List.splitOn, `List.splitOnPTR].contains official then
    checkDataTypes source strict [`List, `Bool, `BEq]
  if official == `List.flatMapMTR.loop then
    checkDataTypes source strict [`List, `Monad, `Applicative, `Pure, `Functor, `Seq, `SeqLeft, `SeqRight, `Bind]
  if official == `BitVec.flattenListFast then
    checkDataTypes source strict [`List]
    for name in [`Omega.BitVec, `Omega.Fin] do
      let some (some field) := impureTrivialStructureInfoExt.find? strict name
        | throw <| IO.userError s!"missing strict bit vector field {name}"
      unless field.fieldIdx == 0 do throw <| IO.userError s!"bit vector field has wrong position {name}"
  if linear official then checkDataTypes source strict [`Prod, `Option, `List, `Nat.Internal.Linear.Expr]
  if listTraversal official then checkDataTypes source strict [`List, `Option]
  if official.getPrefix == `Lean.Grind.CommRing.Mon || official == `Lean.Grind.CommRing.Power.revlex then
    checkDataTypes source strict [`Lean.Grind.CommRing.Mon, `Lean.Grind.CommRing.Power, `Ordering]
  if official == `Lean.RArray.getImpl then checkDataTypes source strict [`Lean.RArray]
  if official.getRoot == `Prod then checkDataTypes source strict [`Prod]
  if official.getRoot == `Fin then
    let some (some field) := impureTrivialStructureInfoExt.find? strict `Omega.Fin | throw <| IO.userError "missing strict Fin layout"
    unless field.fieldIdx == 0 do throw <| IO.userError "unexpected strict Fin value slot"
  let impl ← if official == `withPtrEq then do
    let some fast := source.find? `withPtrEqUnsafe | throw <| IO.userError "missing pinned pointer comparison"
    unless Compiler.getImplementedBy? source official == some fast.name && fast.type == ci.type &&
        checkGuardedPointerEq source do
      throw <| IO.userError "unexpected pointer comparison implementation"
    checkDataTypes source strict [`PUnit, `Bool]
    pure fast.name
  else if official == `List.mapMonoM then do
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

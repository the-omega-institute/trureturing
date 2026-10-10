import LeanInformationAudit.Contract.Literal
import LeanInformationAudit.CompiledAxioms
import LeanInformationAudit.Sha256

namespace LeanInformationAudit.FibApplications
open Lean Contract

def applicationHead : Name := `LeanInformationAudit.AuricFib.Contract.Application

def isInput (info : ConstantInfo) : Bool :=
  info.type.getForallBody.getAppFn.constName? == some applicationHead

private def ref (find : Name → Option ConstantInfo) (value : Expr) : Except String Expr :=
  Literal.referencedValue find value

private def readouts (find : Name → Option ConstantInfo) (value : Expr) : Except String Json := do
  let xs ← Literal.list "fib.readouts" (← ref find value)
  let xs ← xs.mapM fun x => do
    let x ← ref find x
    let head := x.getAppFn.constName?.getD .anonymous
    for name in ["atom", "seam", "guard", "reply"] do
      if head == (`LeanInformationAudit.AuricFib.Contract.Readout).str name then
        return toJson name
    throw "fib.unsupported_readout"
  return Json.arr xs

private def atomBits (find : Name → Option ConstantInfo) (value : Expr) : Except String Json := do
  let x ← ref find value
  let head := x.getAppFn.constName?.getD .anonymous
  let base := `D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window
  for (name, bits) in [("zero", [0,0,0]), ("low", [1,0,0]),
      ("high", [0,1,0]), ("ends", [1,1,0]), ("middle", [0,0,1])] do
    if head == base.str name && x.getAppArgs.isEmpty then return toJson bits
  throw "fib.unsupported_atom"

private def request (find : Name → Option ConstantInfo) (value : Expr) : Except String Json := do
  let evidence ← ref find value
  let args := evidence.getAppArgs
  let head := evidence.getAppFn.constName?.getD .anonymous
  if head == `LeanInformationAudit.AuricFib.Contract.Evidence.unsupported then
    throw (← Literal.string "fib.unsupported" (← ref find args[0]!))
  unless head == `LeanInformationAudit.AuricFib.Contract.Evidence.native && args.size == 4 do
    throw "fib.unsupported_evidence"
  -- The compiled structure supplies reader and same-state continuation equality
  -- proofs. No reader function or audited proof body is executed here.
  discard <| Literal.fields find `LeanInformationAudit.AuricFib.Contract.NativeBridge args[0]! 4
  let acquisition ← ref find args[1]!
  let cells := acquisition.getAppArgs
  let kind := acquisition.getAppFn.constName?.getD .anonymous
  unless cells.size > 0 do throw "fib.unsupported_acquisition"
  let source ← Literal.string "fib.source" (← ref find cells[0]!)
  let mut data : List (String × Json) := []
  let sourceKind ← if kind == `LeanInformationAudit.AuricFib.Contract.Acquisition.absent then
      pure "unknown"
    else if kind == `LeanInformationAudit.AuricFib.Contract.Acquisition.declared && cells.size == 2 then do
      let masses ← Literal.fields find `LeanInformationAudit.AuricFib.Contract.Masses cells[1]! 8
      let denominator ← Literal.nat "fib.denominator" (← ref find masses[5]!)
      let values ← (masses.extract 0 5).mapM fun cell => do
        let n ← Literal.nat "fib.mass" (← ref find cell)
        return toJson s!"{n}/{denominator}"
      data := [("law", Json.arr values)]
      pure "declared-finite-law"
    else if kind == `LeanInformationAudit.AuricFib.Contract.Acquisition.empirical && cells.size == 2 then do
      let values ← (← Literal.list "fib.archive" (← ref find cells[1]!)).mapM (atomBits find)
      data := [("archive", Json.arr values)]
      pure "empirical-archive"
    else throw "fib.unsupported_acquisition"
  return Json.mkObj <| data ++ [
    ("source_contract", Json.mkObj [("kind", toJson sourceKind), ("source", toJson source),
      ("window_length", toJson (1 : Nat)),
      ("native_contract", toJson "initialized-high-to-low-high-suffix")]),
    ("initial_readouts", ← readouts find args[2]!),
    ("layers", ← readouts find args[3]!)]

/-- Fingerprint the actual transitive compiled type/value closure, including
private dependencies. This is data identity, not a source inventory or HEAD key. -/
private def closureIdentity (find : Name → Option ConstantInfo) (roots : Array Name)
    (digests : IO.Ref (NameMap String)) : IO String := do
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := find name | throw <| IO.userError s!"fib.missing_dependency:{name}"
    if !((← digests.get).contains name) then
      let bytes := (reprStr (info.levelParams, info.type, info.value? (allowOpaque := true))).toUTF8
      digests.modify (·.insert name (Sha256.hex bytes))
    pending := (CompiledAxioms.declarationDependencies info).toList ++ pending
  let identities ← seen.toArray.qsort Name.quickLt |>.mapM fun name => do
    return s!"{name}:{((← digests.get).find? name).get!}"
  return Sha256.hex (String.intercalate "\n" identities.toList).toUTF8

/-- Detached source-owned requests. No census or status enters proof assessment. -/
def extract (owner : Name) (constants : Array ConstantInfo)
    (find : Name → Option ConstantInfo) (ownerOf : Name → Option Name) : IO Json := do
  let start ← IO.monoNanosNow
  let mut rows := #[]
  let digests ← IO.mkRef ({} : NameMap String)
  let axiomState ← IO.mkRef ({} : CompiledAxioms.AxiomClosureState)
  for info in constants.qsort (fun a b => a.name.toString < b.name.toString) do
    unless isInput info do continue
    let mut target := Name.anonymous
    let mut sourceOwner := owner
    let mut input := Json.null
    let mut reason := ""
    let decoded := do
      let .defnInfo definition := info | throw "fib.missing_safe_definition"
      unless definition.safety == DefinitionSafety.safe && info.type.getAppArgs.size == 2 do
        throw "fib.unsupported_application_type"
      let occurrence := info.type.getAppArgs[1]!
      let .const name _ := occurrence | throw "fib.target_requires_theorem_constant"
      let some (.thmInfo targetInfo) := find name | throw "fib.target_is_not_theorem"
      unless targetInfo.type == info.type.getAppArgs[0]! do throw "fib.target_type_mismatch"
      let some (.thmInfo native) := find
          `D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber.native_execution
        | throw "fib.native_source_theory_unavailable"
      unless targetInfo.type == native.type do throw "fib.unsupported_target_statement"
      let fs ← Literal.fields find applicationHead definition.value 1
      return (name, ← request find fs[0]!)
    match decoded with
    | .ok (name, value) =>
      target := name
      sourceOwner := (ownerOf name).getD owner
      input := value
    | .error message =>
      reason := message
      if let some name := info.type.getAppArgs[1]?.bind Expr.constName? then
        target := name
        sourceOwner := (ownerOf name).getD owner
    let axioms ← CompiledAxioms.collectAxiomsShared find axiomState info.name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      input := Json.null
      reason := "fib.unaccepted_axiom_closure"
    let identity ← closureIdentity find #[info.name] digests
    let targetIdentity := (find target).map (fun t => Sha256.hex (reprStr t.type).toUTF8)
    rows := rows.push <| Json.mkObj [
      ("application", toJson info.name.toString), ("owner", toJson owner.toString),
      ("target", toJson (if target == .anonymous then none else some target.toString)), ("target_module", toJson sourceOwner.toString),
      ("target_type_identity", toJson targetIdentity), ("input_identity", toJson identity),
      ("request", input), ("unavailable_reason", toJson reason), ("reading", Json.null)]
  if (← IO.getEnv "STRATALINT_INSPECTOR_PROFILE") == some "1" then
    (← IO.getStderr).putStrLn s!"LEAN_INSPECTOR_PROFILE fib_extract_ns={(← IO.monoNanosNow) - start} module={owner} applications={rows.size} dependency_digests={(← digests.get).size}"
  return Json.mkObj [("schema_version", toJson (1 : Nat)), ("applications", Json.arr rows)]

end LeanInformationAudit.FibApplications

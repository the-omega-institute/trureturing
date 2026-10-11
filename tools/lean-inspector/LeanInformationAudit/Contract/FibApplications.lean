import LeanInformationAudit.Contract.FibFinite
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

private def nativeRequest (occurrence : Expr) (info : ConstantInfo)
    (args : Array Expr) : FibSource.M Json := do
  FibSource.indexed `LeanInformationAudit.AuricFib.Contract.NativeSource args[0]! occurrence
  let proof ← CompiledSourceScope.projectField
    `LeanInformationAudit.AuricFib.Contract.NativeSource.reconstruction args[0]!
  let type ← CompiledSourceScope.projectType proof
  unless type.isAppOfArity `LeanInformationAudit.Analysis.Reconstruction 2 do
    FibSource.fail "fib.native_reconstruction_type"
  CompiledSourceScope.reconstruct info.type type.getAppArgs[0]!
  CompiledSourceScope.reconstruct info.type type.getAppArgs[1]!
  let find := (← read).provenance.view.find?
  -- The adapter's compiled reader/source and appended-high/task equalities
  -- retain its exact complete Window domain, including rejected states.
  discard <| FibSource.fields `LeanInformationAudit.AuricFib.Contract.NativeBridge.mk args[1]!
  let acquireLaw : FibSource.M Json := do
    let acquisition ← FibSource.constructorHead args[2]!
    let cells := acquisition.getAppArgs
    let kind := acquisition.getAppFn.constName?.getD .anonymous
    unless cells.size > 0 do FibSource.fail "fib.unsupported_acquisition"
    let source ← IO.ofExcept (Literal.string "fib.source" (← IO.ofExcept (ref find cells[0]!)))
    let mut data : List (String × Json) := []
    let sourceKind ← if kind == `LeanInformationAudit.AuricFib.Contract.Acquisition.absent then
        pure "unknown"
      else if kind == `LeanInformationAudit.AuricFib.Contract.Acquisition.declared && cells.size == 2 then do
        let masses ← IO.ofExcept (Literal.fields find `LeanInformationAudit.AuricFib.Contract.Masses cells[1]! 8)
        let denominator ← IO.ofExcept (Literal.nat "fib.denominator" (← IO.ofExcept (ref find masses[5]!)))
        let values ← (masses.extract 0 5).mapM fun cell => do
          let n ← IO.ofExcept (Literal.nat "fib.mass" (← IO.ofExcept (ref find cell)))
          return toJson s!"{n}/{denominator}"
        data := [("law", Json.arr values)]
        pure "declared-finite-law"
      else if kind == `LeanInformationAudit.AuricFib.Contract.Acquisition.empirical && cells.size == 2 then do
        let values ← IO.ofExcept (do
          (← Literal.list "fib.archive" (← ref find cells[1]!)).mapM (atomBits find))
        data := [("archive", Json.arr values)]
        pure "empirical-archive"
      else FibSource.fail "fib.unsupported_acquisition"
    return Json.mkObj <| data ++ [
      ("source_contract", Json.mkObj [("kind", toJson sourceKind), ("source", toJson source),
        ("window_length", toJson (1 : Nat)),
        ("native_contract", toJson "initialized-high-to-low-high-suffix")]),
      ("initial_readouts", ← IO.ofExcept (readouts find args[3]!)),
      ("layers", ← IO.ofExcept (readouts find args[4]!))]
  try acquireLaw catch error =>
    -- The complete native micro-domain and source correspondence survive an
    -- unavailable law representation. Never replace its law with finite support.
    return Json.mkObj [
      ("source_contract", Json.mkObj [("kind", toJson "unknown"),
        ("source", toJson "compiled source; probability law acquisition unavailable"),
        ("window_length", toJson (1 : Nat)),
        ("native_contract", toJson "initialized-high-to-low-high-suffix")]),
      ("initial_readouts", ← IO.ofExcept (readouts find args[3]!)),
      ("layers", ← IO.ofExcept (readouts find args[4]!)),
      ("law_acquisition", Json.mkObj [("kind", toJson "unavailable"),
        ("reason", toJson error.toString)])]


private def request (original info : ConstantInfo) (occurrence evidence : Expr) : FibSource.M Json := do
  let evidence ← FibSource.constructorHead evidence
  let head := evidence.getAppFn.constName?.getD .anonymous
  let base := `LeanInformationAudit.AuricFib.Contract.Evidence
  if head == base ++ `unsupported then
    let fs ← FibSource.fields head evidence
    let reason ← IO.ofExcept (Literal.string "fib.unsupported" fs[0]!)
    FibSource.fail reason
  if head == base ++ `typed then
    let fs ← FibSource.fields head evidence
    FibFinite.request (← FibSource.bind original info occurrence fs[0]!)
  else if head == base ++ `native then
    let fs ← FibSource.fields head evidence
    let value ← nativeRequest occurrence info fs
    let fields ← IO.ofExcept value.getObj?
    return Json.mkObj (fields.toArray.toList ++ [("binding", Json.mkObj [
      ("occurrence", FibSource.occurrenceBinding original occurrence),
      ("source", FibSource.describe fs[0]!), ("bridge", FibSource.describe fs[1]!),
      ("specialization", Json.mkObj [("seam", toJson false),
        ("composition", toJson [0, 0]), ("history", toJson "[window]"),
        ("continuation_history", toJson "[window, high]"),
        ("scope", toJson "complete initialized single-window fiber; not all histories")]),
      ("ordinary_registration", toJson "independent; no audit status assigned")])])
  else FibSource.fail "fib.unsupported_evidence"

/-- Encode the complete compiler representation without pretty-print layout
search. Length-prefixed text and constructor tags preserve every representation
node, including raw proof bodies, universes, lets, metadata and BinderInfo. -/
private def representationBytes (value : Std.Format) : ByteArray := Id.run do
  let mut pending := [value]
  let mut bytes := "FIB-compiled-repr-format-v1;".toUTF8
  while let node :: rest := pending do
    pending := rest
    let token := match node with
      | .nil => "e"
      | .line => "l"
      | .align force => if force then "a1" else "a0"
      | .text text => s!"t{text.utf8ByteSize}:{text}"
      | .nest indent _ => s!"n{indent}:"
      | .append .. => "p"
      | .group _ behavior =>
        if behavior == Std.Format.FlattenBehavior.fill then "g1" else "g0"
      | .tag tag _ => s!"k{tag}:"
    bytes := bytes ++ token.toUTF8
    match node with
    | .nest _ body | .group body _ | .tag _ body => pending := body :: pending
    | .append left right => pending := left :: right :: pending
    | _ => pure ()
  return bytes

/-- Reuse the source assessor's canonical raw-expression DAG encoding. Its
ordinary bounds are unchanged. Expressions outside that compact format retain
their complete compiler representation through the lossless fallback. -/
private def expressionBytes (params : List Name) (value : Expr) : ByteArray :=
  match TemplateAudit.compactRawEncoding params value with
  | .ok (bytes, _) => "dag:".toUTF8 ++ bytes
  | .error _ => "repr:".toUTF8 ++ representationBytes (repr value)

/-- Fingerprint the actual transitive compiled type/value closure, including
private dependencies. This is data identity, not a source inventory or HEAD key. -/
private def closureIdentity (find : Name → Option ConstantInfo) (roots : Array Name)
    (digests : IO.Ref (NameMap String)) (digest : ByteArray → IO String) : IO String := do
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := find name | throw <| IO.userError s!"fib.missing_dependency:{name}"
    if !((← digests.get).contains name) then
      let levels ← digest (representationBytes (repr info.levelParams))
      let type ← digest (expressionBytes info.levelParams info.type)
      let body ← match info.value? (allowOpaque := true) with
        | some value => digest (expressionBytes info.levelParams value)
        | none => pure "absent"
      let value ← digest s!"FIB-compiled-constant-v2:{levels}:{type}:{body}".toUTF8
      digests.modify (·.insert name value)
    pending := (CompiledAxioms.declarationDependencies info).toList ++ pending
  let identities ← seen.toArray.qsort Name.quickLt |>.mapM fun name => do
    return s!"{name}:{((← digests.get).find? name).get!}"
  digest (String.intercalate "\n" identities.toList).toUTF8

/-- Detached source-owned requests. No census or status enters proof assessment. -/
unsafe def extract (owner : Name) (constants : Array ConstantInfo)
    (store : RawArtifacts.Store)
    (digest : ByteArray → IO String := fun bytes => pure (Sha256.hex bytes)) : IO Json := do
  let start ← IO.monoNanosNow
  let find := store.constants.find?
  let ownerOf := store.owners.find?
  let mut rows := #[]
  let digests ← IO.mkRef ({} : NameMap String)
  let axiomState ← IO.mkRef ({ closure := store.metadata.axioms } : CompiledAxioms.AxiomClosureState)
  for info in constants.qsort (fun a b => a.name.toString < b.name.toString) do
    unless isInput info do continue
    let occurrence? := info.type.getForallBody.getAppArgs[1]?
    let target := occurrence?.bind (·.getAppFn.constName?) |>.getD .anonymous
    let sourceOwner := (ownerOf target).getD owner
    let mut input := Json.null
    let mut reason := ""
    try
      let .defnInfo definition := info | throw <| IO.userError "fib.missing_safe_definition"
      unless definition.safety == DefinitionSafety.safe && info.type.getAppArgs.size == 2 do
        throw <| IO.userError "fib.unsupported_application_type"
      let occurrence := info.type.getAppArgs[1]!
      let .const name levels := occurrence
        | throw <| IO.userError "fib.full_source_occurrence_required"
      let some original@(.thmInfo targetInfo) := find name
        | throw <| IO.userError "fib.target_is_not_theorem"
      unless levels.length == targetInfo.levelParams.length &&
          !occurrence.hasLevelMVar && !occurrence.hasMVar do
        throw <| IO.userError "fib.rigid_universe_arguments"
      let targetType := targetInfo.type.instantiateLevelParams targetInfo.levelParams levels
      unless targetType.equal info.type.getAppArgs[0]! do
        throw <| IO.userError "fib.target_type_mismatch"
      let specialized := ConstantInfo.thmInfo { targetInfo with
        type := targetType, levelParams := info.levelParams }
      let context ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts store owner
        {} (({} : NameSet).insert name)
      let action : FibSource.M Json := do
        let fs ← FibSource.fields (applicationHead ++ `mk) definition.value
        request original specialized occurrence fs[0]!
      input := (← (action.run 524288).run context).1
    catch error => reason := error.toString
    let axioms ← CompiledAxioms.collectAxiomsShared find axiomState info.name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      input := Json.null
      reason := "fib.unaccepted_axiom_closure"
    if input != Json.null then
      let object ← IO.ofExcept input.getObj?
      let binding ← IO.ofExcept (input.getObjVal? "binding" >>= Json.getObj?)
      let binding := Json.mkObj (binding.toArray.toList ++ [
        ("accepted_axioms", toJson (axioms.qsort Name.quickLt |>.map Name.toString))])
      input := Json.mkObj (object.toArray.toList.map fun (key, value) =>
        (key, if key == "binding" then binding else value))
    let identity ← closureIdentity find #[info.name] digests digest
    let targetIdentity := (find target).map (fun t => Sha256.hex (reprStr t.type).toUTF8)
    rows := rows.push <| Json.mkObj [
      ("application", toJson info.name.toString), ("owner", toJson owner.toString),
      ("target", toJson (if target == .anonymous then none else some target.toString)),
      ("target_module", toJson sourceOwner.toString),
      ("target_type_identity", toJson targetIdentity), ("input_identity", toJson identity),
      ("request", input), ("unavailable_reason", toJson reason), ("reading", Json.null)]
  if (← IO.getEnv "STRATALINT_INSPECTOR_PROFILE") == some "1" then
    (← IO.getStderr).putStrLn s!"LEAN_INSPECTOR_PROFILE fib_extract_ns={(← IO.monoNanosNow) - start} module={owner} applications={rows.size} dependency_digests={(← digests.get).size}"
  return Json.mkObj [("schema_version", toJson (1 : Nat)), ("applications", Json.arr rows)]

end LeanInformationAudit.FibApplications

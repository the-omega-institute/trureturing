import LeanInformationAudit.RegistryTypes
import LeanInformationAudit.NameWire
import LeanInformationAudit.Census.Ownership

namespace LeanInformationAudit.CensusStream

open Lean DispositionCensus

/-- The existing syntactic evidence domain; aliases are deliberately outside it. -/
def evidenceTypes : Array Name := #[
  `D5.S3.ConceptDynamics.InformationEscape.Arena.Nondegenerate,
  `D5.S3.ConceptDynamics.InformationEscape.Arena.StateEnumeration,
  `LeanInformationAudit.StructuralRegistrationEvidence,
  `D5.S3.ConceptDynamics.InformationEscape.StructuralCatalog.StructurallyLowersEscape,
  `D5.S3.ConceptDynamics.InformationEscape.StructuralStrictnessCertificate,
  `LeanInformationAudit.BoundedTruncationFamily,
  `LeanInformationAudit.UnreachableElaborationEvidence,
  `LeanInformationAudit.AnalysisDisposition, `LeanInformationAudit.CensusAssessment]

def approximationHead := `LeanInformationAudit.BoundedTruncationFamily.approximation

def evidenceHead (info : ConstantVal) : Option Name :=
  info.type.getAppFn.constName?.filter evidenceTypes.contains

def indexedHead (info : ConstantInfo) : Option Name :=
  if let some head := evidenceHead info.toConstantVal then some head else
  if info.isTheorem then
    match info.type with
    | .forallE _ _ conclusion _ =>
      if conclusion.isAppOfArity approximationHead 3 && !conclusion.hasLooseBVars then
        some approximationHead else none
    | _ => none
  else none

private def stringLiteral? : Expr → Option String
  | .lit (.strVal value) => some value
  | _ => none

/-- Closed constructor syntax can be classified without an Environment. Anything
else is explicitly unknown and cannot establish an absent-candidate row. -/
partial def decodeName? (expr : Expr) : Option Name := do
  let expr := expr.consumeMData
  if expr.isConstOf ``Name.anonymous then return .anonymous
  let args := expr.getAppArgs
  if expr.isAppOfArity ``Name.str 2 then
    return .str (← decodeName? args[0]!) (← stringLiteral? args[1]!)
  if expr.isAppOfArity ``Name.num 2 then
    return .num (← decodeName? args[0]!) (← args[1]!.rawNatLit?)
  -- Lean's ToExpr uses mkStr1 ... mkStr8 for simple names.
  for size in [1:9] do
    if expr.isAppOfArity (.str ``Name ("mkStr" ++ toString size)) size then
      let mut name := Name.anonymous
      for arg in args do name := name.str (← stringLiteral? arg)
      return name
  none

def isSupport (head : Name) : Bool :=
  (evidenceTypes.extract 0 2 ++ evidenceTypes.extract 3 5).contains head ||
    head == approximationHead

private def namedRecord (info : ConstantInfo) (head : Name) : Json := Id.run do
  let args := info.type.getAppArgs
  let mut key := Json.null
  let mut identity := Json.null
  let mut statement := Json.null
  let mut mode := "unknown"
  if isSupport head then mode := "support"
  else if head == `LeanInformationAudit.StructuralRegistrationEvidence then
    if let some name := args[0]?.bind decodeName? then
      key := nameJson name
      mode := "name"
  else if head == `LeanInformationAudit.AnalysisDisposition ||
      head == `LeanInformationAudit.CensusAssessment then
    if let some expr := args[0]? then
      if expr.isAppOfArity `LeanInformationAudit.StatementKey.mk 2 then
        if let (some name, some id) :=
            (decodeName? expr.getAppArgs[0]!, stringLiteral? expr.getAppArgs[1]!) then
          key := nameJson name
          identity := toJson id
          mode := "key"
  else if head == `LeanInformationAudit.BoundedTruncationFamily ||
      head == `LeanInformationAudit.UnreachableElaborationEvidence then
    if let some expr := args[0]? then
      statement := toJson (toString expr)
      mode := "statement"
  return Json.mkObj [("name", nameJson info.name), ("head", toJson head.toString),
    ("mode", toJson mode), ("key", key), ("identity", identity), ("statement", statement)]

/-- Entry layouts come from their producer's actual types, not probe copies.
The casts have the same trusted olean boundary as Lean's extension importer. -/
private unsafe def registryRecords (data : ModuleData) : Json := Id.run do
  let mut finite := #[]
  let mut structural := #[]
  let mut seals := #[]
  for (name, entries) in data.entries do
    let name := privateToUserName name
    if name == `LeanInformationAudit.informationRegistryExt then
      for raw in entries do
        let entry : InformationRegistryEntry := unsafeCast raw
        finite := finite.push <| Json.mkObj [
          ("key", nameJson entry.theoremName), ("module", toJson entry.registrationModuleName.toString),
          ("names", Json.arr #[nameJson entry.unitName, nameJson entry.realizationName])]
    else if name == `LeanInformationAudit.DispositionCensus.structuralRegistry then
      for raw in entries do
        let entry : StructuralProvenanceEntry := unsafeCast raw
        structural := structural.push <| Json.mkObj [
          ("key", nameJson entry.theoremName), ("module", toJson entry.registrationModule.toString),
          ("names", Json.arr #[nameJson entry.unitConst, nameJson entry.realizationConst])]
    else if name == `LeanInformationAudit.sealRecordExt then
      for raw in entries do
        let entry : SealArenaRecord := unsafeCast raw
        seals := seals.push (toJson entry.catalog.rootId.toString)
  return Json.mkObj [("finite", Json.arr finite), ("structural", Json.arr structural),
    ("seals", Json.arr seals)]

@[noinline] private unsafe def emitData (moduleName part : String) (data : ModuleData)
    (keys : Std.HashSet Name) (out : IO.FS.Stream) : IO Unit := do
  let mut named := #[]
  for info in data.constants do
    if let some head := indexedHead info then named := named.push (namedRecord info head)
  let imports := data.imports.map fun entry => Json.mkObj [
    ("module", toJson entry.module.toString), ("all", toJson entry.importAll),
    ("exported", toJson entry.isExported), ("meta", toJson entry.isMeta)]
  out.putStrLn (Json.mkObj [("module", toJson moduleName), ("part", toJson part),
    ("is_module", toJson data.isModule), ("imports", Json.arr imports),
    ("owners", Json.arr #[]), ("named", Json.arr named),
    ("registries", registryRecords data)]).compress

  -- Statement identities for collisions are supplied by the standalone producer.
  for info in data.constants do
    unless keys.contains info.name do continue
    let owner := Json.mkObj [("name", nameJson info.name),
      ("matches", toJson (CensusOwnership.moduleContainsTheorem data info)),
      ("kind", toJson (if info.isTheorem then "theorem" else "other"))]
    out.putStrLn (Json.mkObj [("module", toJson moduleName), ("part", toJson part),
      ("owner", owner)]).compress

/-- A noinline boundary releases all region-backed Name/Expr/JSON references
before freeing parts in reverse dependency order. Parts are never loaded alone.
J3's generated roots have no `module` declaration: Lean imports them at the
private level, so all available parts and private import edges are in scope. -/
@[noinline] private unsafe def readAndEmit (moduleName : String) (paths : Array String)
    (keys : Std.HashSet Name) (out : IO.FS.Stream) : IO (Array CompactedRegion) := do
  let parts ← readModuleDataParts (paths.map System.FilePath.mk)
  let mut regions := #[]
  for h : i in [:parts.size] do
    let (data, region) := parts[i]
    emitData moduleName (#["base", "server", "private"][i]!) data keys out
    regions := regions.push region
  return regions

unsafe def scan (manifest request destination : String) : IO Unit := do
  let input ← IO.ofExcept <| Json.parse (← IO.FS.readFile request)
  let requests ← IO.ofExcept <| input.getObjValAs? (Array (Array String)) "keys"
  let mut keys : Std.HashSet Name := {}
  for row in requests do
    unless row.size == 3 do throw <| IO.userError "IE-C044 invalid request triple"
    keys := keys.insert (← IO.ofExcept <| parseNameKey row[1]!)
  let input ← IO.ofExcept <| Json.parse (← IO.FS.readFile manifest)
  let modules ← IO.ofExcept <| fromJson? (α := Array (String × Array String)) input
  let out ← if destination == "-" then IO.getStdout else
    IO.FS.Stream.ofHandle <$> IO.FS.Handle.mk destination .write
  for (moduleName, paths) in modules do
    unless paths.size ≥ 1 && paths.size ≤ 3 do
      throw <| IO.userError "IE-C044 expected a prefix of olean parts"
    let regions ← readAndEmit moduleName paths keys out
    for region in regions.reverse do region.free
    out.flush
  out.flush

end LeanInformationAudit.CensusStream

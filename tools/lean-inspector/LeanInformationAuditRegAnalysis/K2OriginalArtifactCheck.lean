import Lean

open Lean

namespace K2OriginalArtifactCheck

private def valueMatches (left right : ConstantInfo) : Bool :=
  match left.value? (allowOpaque := true), right.value? (allowOpaque := true) with
  | none, none => true
  | some a, some b => a.equal b
  | _, _ => false

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def layout : ConstantInfo → Json
  | .ctorInfo info => Json.mkObj [
      ("inductive", toJson info.induct), ("index", toJson info.cidx),
      ("parameters", toJson info.numParams), ("fields", toJson info.numFields)]
  | .inductInfo info => Json.mkObj [
      ("parameters", toJson info.numParams), ("indices", toJson info.numIndices),
      ("constructors", toJson info.ctors), ("recursive", toJson info.isRec)]
  | .recInfo info => Json.mkObj [
      ("parameters", toJson info.numParams), ("indices", toJson info.numIndices),
      ("motives", toJson info.numMotives), ("minors", toJson info.numMinors)]
  | _ => Json.null

private def compare (original rebuilt : ModuleData) : Json := Id.run do
  let publicConstant := fun info : ConstantInfo => !info.name.isInternal
  let originalPublic := original.constants.filter publicConstant
  let rebuiltPublic := rebuilt.constants.filter publicConstant
  let oldMap := originalPublic.foldl (fun table info => table.insert info.name info)
    ({} : Std.HashMap Name ConstantInfo)
  let newMap := rebuiltPublic.foldl (fun table info => table.insert info.name info)
    ({} : Std.HashMap Name ConstantInfo)
  let mut differences : Array Json := #[]
  let mut constructors : Array Json := #[]
  for left in originalPublic do
    let some right := newMap[left.name]? | do
      differences := differences.push <| Json.mkObj [
        ("name", toJson left.name), ("difference", toJson "missing_rebuilt")]
      continue
    let typeEqual := left.type.equal right.type
    let valueEqual := valueMatches left right
    let levelsEqual := left.levelParams == right.levelParams
    let kindEqual := kind left == kind right
    let layoutEqual := layout left == layout right
    unless typeEqual && valueEqual && levelsEqual && kindEqual && layoutEqual do
      differences := differences.push <| Json.mkObj [
        ("name", toJson left.name), ("typeEqual", toJson typeEqual),
        ("valueEqual", toJson valueEqual), ("levelParametersEqual", toJson levelsEqual),
        ("kindEqual", toJson kindEqual), ("layoutEqual", toJson layoutEqual),
        ("originalType", toJson left.type.dbgToString),
        ("rebuiltType", toJson right.type.dbgToString),
        ("originalValue", toJson ((left.value? (allowOpaque := true)).map Expr.dbgToString)),
        ("rebuiltValue", toJson ((right.value? (allowOpaque := true)).map Expr.dbgToString)),
        ("originalLayout", layout left), ("rebuiltLayout", layout right)]
    if kind left == "constructor" then
      constructors := constructors.push <| Json.mkObj [
        ("name", toJson left.name), ("original", layout left), ("rebuilt", layout right),
        ("equal", toJson layoutEqual)]
  for right in rebuiltPublic do
    unless oldMap.contains right.name do
      differences := differences.push <| Json.mkObj [
        ("name", toJson right.name), ("difference", toJson "extra_rebuilt")]
  return Json.mkObj [
    ("originalConstants", toJson original.constants.size),
    ("rebuiltConstants", toJson rebuilt.constants.size),
    ("originalPublicConstants", toJson originalPublic.size),
    ("rebuiltPublicConstants", toJson rebuiltPublic.size),
    ("publicRawDeclarationsEqual", toJson differences.isEmpty),
    ("differences", toJson differences), ("constructors", toJson constructors),
    ("originalImports", toJson (original.imports.map (·.module))),
    ("rebuiltImports", toJson (rebuilt.imports.map (·.module))),
    ("originalExtensions", toJson (original.entries.map (fun (name, entries) =>
      Json.mkObj [("name", toJson name), ("entries", toJson entries.size)]))),
    ("rebuiltExtensions", toJson (rebuilt.entries.map (fun (name, entries) =>
      Json.mkObj [("name", toJson name), ("entries", toJson entries.size)]))),
    ("metadataStripped", toJson false),
    ("comparison", toJson "Expr.equal including binder names/annotations; no inference/reduction/defeq; persistent extension state not compared")]

-- Insert inside K2OriginalArtifactCheck; the parent owns repository edits/builds.
private def expressionReferences (expression : Expr) : Array Name := Id.run do
  let mut pending := #[expression]
  let mut visited : Std.HashSet Expr := {}
  let mut references : NameSet := {}
  while let some node := pending.back? do
    pending := pending.pop
    if visited.contains node then continue
    visited := visited.insert node
    match node with
    | .const name _ => references := references.insert name
    | .proj name _ value =>
      references := references.insert name
      pending := pending.push value
    | .app function argument => pending := pending.push function |>.push argument
    | .lam _ domain body _ | .forallE _ domain body _ =>
      pending := pending.push domain |>.push body
    | .letE _ domain value body _ => pending := pending.push domain |>.push value |>.push body
    | .mdata _ value => pending := pending.push value
    | _ => pure ()
  return references.toArray

private def rawReferences (info : ConstantInfo) : Array Name := Id.run do
  let mut refs := expressionReferences info.type
  if let some value := info.value? (allowOpaque := true) then
    refs := refs ++ expressionReferences value
  match info with
  | .inductInfo value => refs := refs ++ value.all.toArray ++ value.ctors.toArray
  | .ctorInfo value => refs := refs.push value.induct
  | .recInfo value =>
    refs := refs ++ value.all.toArray
    for rule in value.rules do
      refs := refs.push rule.ctor ++ expressionReferences rule.rhs
  | _ => pure ()
  return refs

private def rawRecursorRulesEqual (left right : ConstantInfo) : Bool :=
  match left, right with
  | .recInfo a, .recInfo b =>
    a.all == b.all && a.k == b.k && a.isUnsafe == b.isUnsafe &&
      a.rules.length == b.rules.length &&
      (a.rules.zip b.rules).all (fun (x, y) =>
        x.ctor == y.ctor && x.nfields == y.nfields && x.rhs.equal y.rhs)
  | .recInfo _, _ | _, .recInfo _ => false
  | _, _ => true

private def commonAllDifferences (original rebuilt : ModuleData) : Array Json := Id.run do
  let newMap := rebuilt.constants.foldl (fun table info => table.insert info.name info)
    ({} : Std.HashMap Name ConstantInfo)
  let mut result := #[]
  for left in original.constants do
    let some right := newMap[left.name]? | continue
    unless left.type.equal right.type && valueMatches left right &&
        left.levelParams == right.levelParams && kind left == kind right &&
        left.isUnsafe == right.isUnsafe &&
        layout left == layout right && rawRecursorRulesEqual left right do
      result := result.push <| Json.mkObj [
        ("name", toJson left.name), ("internal", toJson left.name.isInternal),
        ("typeEqual", toJson (left.type.equal right.type)),
        ("valueEqual", toJson (valueMatches left right)),
        ("levelsEqual", toJson (left.levelParams == right.levelParams)),
        ("kindEqual", toJson (kind left == kind right)),
        ("unsafeEqual", toJson (left.isUnsafe == right.isUnsafe)),
        ("layoutEqual", toJson (layout left == layout right)),
        ("recursorRulesEqual", toJson (rawRecursorRulesEqual left right))]
  return result

private def forbiddenReferenceAudit
    (modules : Array (Name × ModuleData)) (forbidden : NameSet) : Json := Id.run do
  let mut edges : Array Json := #[]
  let mut constants := 0
  let mut references := 0
  for (module, data) in modules do
    for info in data.constants do
      -- The additional declarations themselves are outside the common/consumed schema.
      if forbidden.contains info.name then continue
      constants := constants + 1
      for ref in rawReferences info do
        references := references + 1
        if forbidden.contains ref then
          edges := edges.push <| Json.mkObj [
            ("module", toJson module), ("declaration", toJson info.name),
            ("referencedAddition", toJson ref)]
  return Json.mkObj [
    ("modules", toJson modules.size), ("scannedConstants", toJson constants),
    ("scannedReferenceOccurrences", toJson references),
    ("completeExprTraversal", toJson true),
    ("referencesToUnsharedAdditions", toJson edges),
    ("passed", toJson edges.isEmpty),
    ("scope", toJson "all raw const/projection-name type/value references and inductive/constructor/recursor links in supplied modules, including private constants and recursor rule right-hand sides; no inference/reduction/defeq")]

end K2OriginalArtifactCheck

unsafe def main (args : List String) : IO UInt32 := do
  let (originalPrefix, rebuiltPrefix, regPrefix, regModulesFile, output) ← match args with
    | [originalPrefix, rebuiltPrefix, regPrefix, regModulesFile, output] =>
      pure (originalPrefix, rebuiltPrefix, regPrefix, regModulesFile, output)
    | _ => throw <| IO.userError "ORIGINAL_PREFIX REBUILT_PREFIX REG_PREFIX REG_MODULES OUTPUT required"
  let modules := #["Contract/Core", "Contract/NodeFactsCore", "Contract/Implementation", "Contract/Catalog"]
  let mut records : Array Json := #[]
  let mut regions : Array CompactedRegion := #[]
  let mut passed := true
  let mut commonEqual := true
  let mut additions : NameSet := {}
  let mut scanned : Array (Name × ModuleData) := #[]
  for module in modules do
    let relative := "LeanInformationAuditInterface/" ++ module ++ ".olean"
    let (original, oldRegion) ← readModuleData (originalPrefix ++ "/" ++ relative)
    let (rebuilt, newRegion) ← readModuleData (rebuiltPrefix ++ "/" ++ relative)
    regions := regions.push oldRegion |>.push newRegion
    let row := K2OriginalArtifactCheck.compare original rebuilt
    passed := passed && (row.getObjValAs? Bool "publicRawDeclarationsEqual").toOption.getD false
    let differences := K2OriginalArtifactCheck.commonAllDifferences original rebuilt
    commonEqual := commonEqual && differences.isEmpty
    let rebuiltNames := rebuilt.constants.foldl (fun names info => names.insert info.name)
      ({} : NameSet)
    for info in original.constants do
      unless rebuiltNames.contains info.name do additions := additions.insert info.name
    let owner := ("LeanInformationAuditInterface/" ++ module).replace "/" "." |>.toName
    scanned := scanned.push (owner, original)
    records := records.push <| (row.setObjVal! "module" (toJson module)).setObjVal!
      "commonAllDifferences" (toJson differences)
  for module in #["Records", "SourceSelection", "Store", "OutputSyntax", "RootContract", "Syntax",
      "Contract/NodeFacts", "Contract/Registration"] do
    let path := originalPrefix ++ "/LeanInformationAuditInterface/" ++ module ++ ".olean"
    let (data, region) ← readModuleData path
    regions := regions.push region
    scanned := scanned.push (("LeanInformationAuditInterface/" ++ module).replace "/" "." |>.toName, data)
  let regModules := (← IO.FS.readFile regModulesFile).splitOn "\n" |>.filter (· != "")
  unless regModules.length == 418 && regModules.toArray.toList.eraseDups.length == 418 do
    throw <| IO.userError "complete418originalRegInventoryRequired"
  for module in regModules do
    let (data, region) ← readModuleData (regPrefix ++ "/" ++ module.replace "." "/" ++ ".olean")
    regions := regions.push region
    scanned := scanned.push (module.toName, data)
  let dependency := K2OriginalArtifactCheck.forbiddenReferenceAudit scanned additions
  let compatible := commonEqual && (dependency.getObjValAs? Bool "passed").toOption.getD false
  let result := Json.mkObj [
    ("modules", toJson records), ("passed", toJson passed),
    ("commonRawDeclarationsEqual", toJson commonEqual),
    ("unsharedAdditions", toJson additions.toArray),
    ("dependencyAudit", dependency),
    ("restoredInputsCompatible", toJson compatible),
    ("compactedRegionsRetained", toJson regions.size),
    ("scope", toJson "common raw interface declarations including private constants and recursor rules; all418originalReg modules plus12retained interface modules have no raw edge into unshared additions; no olean byte or persistent extension equivalence claim")]
  IO.FS.writeFile output (result.pretty ++ "\n")
  IO.println result.compress
  return if compatible then 0 else 1

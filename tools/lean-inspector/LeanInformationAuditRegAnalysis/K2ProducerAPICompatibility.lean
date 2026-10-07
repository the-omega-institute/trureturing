import Lean

open Lean

namespace K2ProducerAPICompatibility

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

private partial def typeConstructorType : Expr → Bool
  | .sort _ => true
  | .forallE _ _ body _ | .letE _ _ _ body _ | .mdata _ body => typeConstructorType body
  | _ => false

private def declarationsEqual (left right : ConstantInfo) : Bool :=
  left.type.equal right.type &&
    (!typeConstructorType left.type || valueMatches left right) &&
    left.levelParams == right.levelParams && kind left == kind right &&
    left.isUnsafe == right.isUnsafe && layout left == layout right &&
    rawRecursorRulesEqual left right

end K2ProducerAPICompatibility

unsafe def main (args : List String) : IO UInt32 := do
  let (baselinePrefix, currentPrefix, generatorPrefix, modulesFile, output) ← match args with
    | [baselinePrefix, currentPrefix, generatorPrefix, modulesFile, output] =>
      pure (baselinePrefix, currentPrefix, generatorPrefix, modulesFile, output)
    | _ => throw <| IO.userError "BASELINE_PRODUCER CURRENT_PRODUCER GENERATOR MODULES OUTPUT required"
  let modules := (← IO.FS.readFile modulesFile).splitOn "\n" |>.filter (· != "")
  unless modules.length == 12 && modules.eraseDups.length == 12 do
    throw <| IO.userError "exact12ProducerModuleInventoryRequired"
  let mut baseline : Std.HashMap Name ConstantInfo := {}
  let mut current : Std.HashMap Name ConstantInfo := {}
  let mut regions : Array CompactedRegion := #[]
  for module in modules do
    let relative := module.replace "." "/" ++ ".olean"
    let (old, oldRegion) ← readModuleData (baselinePrefix ++ "/" ++ relative)
    let (new, newRegion) ← readModuleData (currentPrefix ++ "/" ++ relative)
    regions := regions.push oldRegion |>.push newRegion
    for info in old.constants do baseline := baseline.insert info.name info
    for info in new.constants do current := current.insert info.name info
  let generatorModules := #[
    "LeanInformationAuditRegAnalysis.K2FactsGenerator",
    "LeanInformationAuditRegAnalysis.K2FactsGeneratorCore",
    "LeanInformationAuditRegAnalysis.K2HeadFamiliesGenerator",
    "LeanInformationAuditRegAnalysis.K2PostprocessGenerator"]
  let mut actualRoots : NameSet := {}
  let mut scannedGeneratorConstants := 0
  let mut scannedGeneratorReferenceOccurrences := 0
  for module in generatorModules do
    let (data, region) ← readModuleData
      (generatorPrefix ++ "/" ++ module.replace "." "/" ++ ".olean")
    regions := regions.push region
    for info in data.constants do
      scannedGeneratorConstants := scannedGeneratorConstants + 1
      for name in K2ProducerAPICompatibility.rawReferences info do
        scannedGeneratorReferenceOccurrences := scannedGeneratorReferenceOccurrences + 1
        if baseline.contains name || current.contains name then
          actualRoots := actualRoots.insert name
  let expectedRoots : NameSet := #[
    `LeanInformationAudit.Contract.Literal.array,
    `LeanInformationAudit.Contract.Literal.fields,
    `LeanInformationAudit.Contract.Literal.instantiateRawLevels,
    `LeanInformationAudit.Contract.Literal.name,
    `LeanInformationAudit.Contract.Literal.optional,
    `LeanInformationAudit.Contract.Literal.referencedValue,
    `LeanInformationAudit.Contract.Literal.resolveReferences,
    `LeanInformationAudit.RegistrationGates.compiledModuleClasses].foldl
      (fun set name => set.insert name) {}
  let mut pending := actualRoots.toList
  let mut seen : NameSet := {}
  let mut differences : Array Json := #[]
  let mut compatible : Array Json := #[]
  let mut external : NameSet := {}
  let mut dependencyReferenceOccurrences := 0
  while let name :: rest := pending do
    pending := rest
    if seen.contains name then continue
    seen := seen.insert name
    let old := baseline[name]?
    let new := current[name]?
    match old, new with
    | some left, some right =>
      let equal := K2ProducerAPICompatibility.declarationsEqual left right
      if equal then compatible := compatible.push <| Json.mkObj [
        ("name", toJson name), ("kind", toJson (K2ProducerAPICompatibility.kind left))]
      else differences := differences.push <| Json.mkObj [
        ("name", toJson name), ("typeEqual", toJson (left.type.equal right.type)),
        ("implementationBodyEqual", toJson (K2ProducerAPICompatibility.valueMatches left right)),
        ("bodyEqualityRequiredForTypeConstructor", toJson (K2ProducerAPICompatibility.typeConstructorType left.type)),
        ("levelsEqual", toJson (left.levelParams == right.levelParams)),
        ("kindEqual", toJson (K2ProducerAPICompatibility.kind left == K2ProducerAPICompatibility.kind right)),
        ("unsafeEqual", toJson (left.isUnsafe == right.isUnsafe)),
        ("layoutEqual", toJson (K2ProducerAPICompatibility.layout left == K2ProducerAPICompatibility.layout right)),
        ("recursorRulesEqual", toJson (K2ProducerAPICompatibility.rawRecursorRulesEqual left right))]
    | _, _ => differences := differences.push <| Json.mkObj [
        ("name", toJson name), ("baselinePresent", toJson old.isSome),
        ("currentPresent", toJson new.isSome)]
    for info in old.toArray ++ new.toArray do
      let mut references := K2ProducerAPICompatibility.expressionReferences info.type
      if K2ProducerAPICompatibility.typeConstructorType info.type then
        if let some value := info.value? (allowOpaque := true) then
          references := references ++ K2ProducerAPICompatibility.expressionReferences value
      references := match info with
        | .inductInfo value => references ++ value.all.toArray ++ value.ctors.toArray
        | .ctorInfo value => references.push value.induct
        | .recInfo value => references ++ value.all.toArray ++ value.rules.toArray.map (·.ctor)
        | _ => references
      for reference in references do
        dependencyReferenceOccurrences := dependencyReferenceOccurrences + 1
        if baseline.contains reference || current.contains reference then
          pending := reference :: pending
        else external := external.insert reference
  let unexpected := actualRoots.toList.filter fun name => !expectedRoots.contains name
  let unusedExpected := expectedRoots.toList.filter fun name => !actualRoots.contains name
  let result := Json.mkObj [
    ("passed", toJson differences.isEmpty),
    ("baselineProducerPrefix", toJson baselinePrefix),
    ("currentProducerPrefix", toJson currentPrefix),
    ("generatorPrefix", toJson generatorPrefix),
    ("producerModules", toJson modules), ("generatorModules", toJson generatorModules),
    ("scannedGeneratorConstants", toJson scannedGeneratorConstants),
    ("scannedGeneratorReferenceOccurrences", toJson scannedGeneratorReferenceOccurrences),
    ("completeExprTraversal", toJson true),
    ("actualProducerRoots", toJson actualRoots.toArray),
    ("sourceInventoryRoots", toJson expectedRoots.toArray),
    ("additionalActualRoots", toJson unexpected),
    ("unusedSourceInventoryRoots", toJson unusedExpected),
    ("comparedProducerClosureDeclarations", toJson seen.size),
    ("dependencyReferenceOccurrences", toJson dependencyReferenceOccurrences),
    ("compatibleDeclarations", toJson compatible), ("differences", toJson differences),
    ("externalBoundaryReferences", toJson external.toArray),
    ("compactedRegionsRetained", toJson regions.size),
    ("scope", toJson "complete raw constant/projection/type/value/recursor-rule references of four frozen generator modules discover actual consumed producer API roots; transitive raw type/type-constructor-body/inductive/constructor/recursor-link closure through both 12-module inventories checks raw types/type-constructor meaning/levels/kinds/unsafe/layout/recursor rules; ordinary implementation bodies may differ and are not reuse or compatibility conditions; original-input environment separately uses exact baseline source/object snapshots; no inference/reduction/defeq or persistent extension equivalence claim")]
  IO.FS.writeFile output (result.pretty ++ "\n")
  IO.println result.compress
  return if differences.isEmpty then 0 else 1

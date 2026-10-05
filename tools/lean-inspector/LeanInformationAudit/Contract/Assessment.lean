import LeanInformationAudit.Contract.Discovery

namespace LeanInformationAudit.TypedAssessment
open LeanInformationAudit.Contract
open Lean Meta Elab Command

/-- Discover the target import closure from compiled declarations and source paths. -/
def targetSnapshot (root : Name) : MetaM Discovery.Snapshot := do
  let env ← getEnv
  let reachable := reachableModules (moduleImports env) root
  let owners := (env.header.moduleNames.push env.header.mainModule).filter fun owner =>
    reachable.contains owner && (`Reg).isPrefixOf owner
  let requirements ← RootStructure.requiredFor owners Discovery.moduleSource
  Discovery.discoverWithStructure requirements owners

private def publish (owner name : Name) (value : Expr) (isTheorem : Bool) (levelParams : Option (List Name) := none)
    (computable : Bool := false) : MetaM Unit := do
  let value ← instantiateMVars value
  let type ← instantiateMVars (← inferType value)
  unless Literal.closed value && Literal.closed type do
    throwError "incomplete_closure:contract.companion_open:{name}"
  let levels := levelParams.getD
    (collectLevelParams (collectLevelParams {} type) value).params.toList
  if let some previous := (← getEnv).find? name then
    let sameType ← isDefEq previous.type type
    unless previous.levelParams == levels && sameType &&
        previous.value? (allowOpaque := true) == some value do
      throwError "contract.companion_collision:{name}"
  else
    GeneratedDeclarations.withOwner owner do
      let declaration := if isTheorem then .thmDecl { name, levelParams := levels, type, value }
        else .defnDecl { name, levelParams := levels, type, value, hints := .abbrev, safety := .safe }
      if computable then addAndCompile declaration else addDecl declaration
      modifyEnv (GeneratedDeclarations.record · name)
      unless isTheorem || computable do modifyEnv (addNoncomputable · name)

/-- Publish stable aliases of the original compiled values. -/
def prepareCompanions (owner : Name) (row : Decoder.CompanionInput) : MetaM Unit := do
  let entry := row.input.entry
  if entry.sourceBound then
    let record ← getConstInfo entry.realizationName
    publish owner entry.unitName
      (mkConst entry.realizationName (record.levelParams.map Level.param)) false
      (some record.levelParams)
    return
  if row.generated || row.bridge.constName? != some entry.realizationName then
    publish owner entry.realizationName row.bridge true
  let some unit := row.unit | throwError "contract.registration:unit_missing"
  let computationalInputs := unit.getUsedConstants
  let env ← getEnv
  publish owner entry.unitName unit false none
    (!computationalInputs.any (isNoncomputable env ·))

/-- One decoded snapshot supplies all assessment inputs; no raw-input environment
extension, source re-elaboration or native evaluation participates. -/
def assessSnapshot (snapshot : Discovery.Snapshot) : MetaM Unit := do
  modifyEnv fun env => RootCatalogs.install
    (TemplateAudit.resetTemplatePlans <| TemplateBinding.resetAssessmentRecords <|
      InformationRegistry.reset env) (snapshot.roots.map Prod.snd)
  for (_, catalog) in snapshot.roots do RootCatalogs.acquireProvenance catalog
  liftCommandElabM do
    for (owner, enrollment) in snapshot.enrollments do assessRecordedEnrollment owner enrollment
    for (owner, row) in snapshot.registrations do
      GeneratedDeclarations.withOwner owner do
        liftTermElabM <| prepareCompanions owner row
        assessRecordedEntry owner row.input

end LeanInformationAudit.TypedAssessment

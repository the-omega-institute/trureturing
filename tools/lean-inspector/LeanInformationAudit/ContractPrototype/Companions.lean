import LeanInformationAudit.ContractPrototype.Discovery

/- L0 原型 -/
namespace LeanInformationAudit.ContractPrototype
open Lean Meta

private def publish (owner : Name) (name : Name) (type value : Expr)
    (isTheorem : Bool) : MetaM Unit := GeneratedDeclarations.withOwner owner do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar then
    throwError "incomplete_closure:contract.companion_open:{name}"
  let levels := (collectLevelParams (collectLevelParams {} type) value).params.toList
  if let some existing := (← getEnv).find? name then
    unless existing.levelParams == levels && existing.type.equal type &&
        existing.value? (allowOpaque := true) == some value do
      throwError "incomplete_closure:contract.companion_collision:{name}"
    return
  if isTheorem then
    addDecl (.thmDecl { name, levelParams := levels, type, value })
  else
    let declaration := Declaration.defnDecl {
      name, levelParams := levels, type, value
      hints := .abbrev, safety := .safe }
    if value.getUsedConstants.any (isNoncomputable (← getEnv) ·) then
      addDecl declaration
      modifyEnv (addNoncomputable · name)
    else
      addAndCompile declaration
  modifyEnv (GeneratedDeclarations.record · name)

/-- Build kernel-checked report companions without executing a readout or proof.
The caller supplies the typed field retained by the discovery snapshot. -/
def prepareCompanions (owner : Name) (input : RegistrationInput)
    (payload : CompanionInput) : MetaM Unit := do
  let entry := input.entry
  unless payload.input.entry.unitName == entry.unitName &&
      entry.registrationModuleName == owner do
    throwError "incomplete_closure:contract.companion_owner"
  let theoremExpr := payload.target
  let statement ← inferType theoremExpr
  let bridge ← if (← getEnv).contains entry.realizationName then do
      let bridge ← mkConstWithFreshMVarLevels entry.realizationName
      unless ← isDefEq (← inferType bridge) (← inferType payload.bridge) do
        throwError "unclassified_form:contract.bridge_alias:{entry.realizationName}"
      unless ← isDefEq bridge payload.bridge do
        throwError "unclassified_form:contract.bridge_value:{entry.realizationName}"
      pure (← instantiateMVars bridge)
    else do
      let type ← inferType payload.bridge
      publish owner entry.realizationName type payload.bridge true
      mkConstWithFreshMVarLevels entry.realizationName
  let bridgeType ← whnfR (← inferType bridge)
  let args := bridgeType.getAppArgs
  if entry.sourceBound then
    unless bridgeType.isAppOfArity
        `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration 2 do
      throwError "unclassified_form:contract.source_bridge"
    unless ← isDefEq args[1]! statement do
      throwError "unclassified_form:contract.source_statement"
    let bridge ← instantiateMVars bridge
    publish owner entry.unitName (← inferType bridge) bridge false
    return
  unless args.size == 3 && (← isDefEq args[1]! statement) do
    throwError "IE-C006 StatementProofMismatch: {entry.theoremName}"
  let unit ← if bridgeType.isAppOf
      `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization then
      mkAppM `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit
        #[bridge, theoremExpr]
    else if bridgeType.isAppOf RegistrationElaboration.witnessBridgeName then do
      let some positive := payload.positive
        | throwError "unclassified_form:dtr.witness_bridge_requires_positive_variation"
      mkAppM (RegistrationElaboration.witnessBridgeName.str "toTheoremUnit") #[bridge, positive]
    else if bridgeType.isAppOf TemplateAudit.escapeForwardBridge then do
      let some primitives := input.suppliedPrimitives
        | throwError "IE-C006 StatementProofMismatch: {entry.theoremName}"
      mkAppM `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.mk
        #[primitives, statement, theoremExpr]
    else throwError "IE-C006 StatementProofMismatch: {entry.theoremName}"
  publish owner entry.unitName (← inferType unit) unit false

end LeanInformationAudit.ContractPrototype

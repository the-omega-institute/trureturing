import LeanInformationAudit.Registry

namespace LeanInformationAudit

open Lean
open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Term
open Lean.Meta

private def theoremUnitSuffix := "__information_unit"

private def declarationName (id : TSyntax `ident) : CommandElabM Name := do
  let name := id.getId
  if (`_root_).isPrefixOf name then
    return name.replacePrefix `_root_ .anonymous
  return (← getCurrNamespace) ++ name

private def absoluteIdentFrom (ref : Syntax) (name : Name) : Ident :=
  mkIdentFrom ref (`_root_ ++ name)

private def ensureRegisterableName (env : Environment) (theoremName : Name) :
    CommandElabM Unit := do
  if isCompanionName theoremName then
    throwError "IE-C011 GeneratedCertificateRegistered: {theoremName}"
  if InformationRegistry.hasTheorem env theoremName then
    throwError "IE-C002 DuplicateRegistration: {theoremName}"

private def resolveTheorem (id : TSyntax `ident) : CommandElabM Name := do
  let theoremName <- try
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  catch _ =>
    throwErrorAt id
      "IE-C001 UnregisteredTheoremUnit: {← declarationName id}"
  match (← getEnv).find? theoremName with
  | some (.thmInfo _) => pure theoremName
  | _ => throwErrorAt id "IE-C001 UnregisteredTheoremUnit: {theoremName}"

private def registerEntry (entry : InformationRegistryEntry) : CommandElabM Unit := do
  let result <- liftTermElabM <| validateEntryTypes (← getEnv) entry
  match result with
  | .ok () =>
      modifyEnv fun env => informationRegistryExt.addEntry env entry
  | .error message => throwError message

private def checkLegacyBinding (theoremName arenaName realizationName : Name)
    (primitiveTerm : TSyntax `term) :
    CommandElabM Unit := do
  let valid <- liftTermElabM do
    try
      let theoremExpr <- mkConstWithFreshMVarLevels theoremName
      let theoremType <- instantiateMVars (← whnfR (← inferType theoremExpr))
      let arenaExpr <- mkConstWithFreshMVarLevels arenaName
      let arenaType <- instantiateMVars (← whnfR (← inferType arenaExpr))
      unless arenaType.getAppFn.constName? ==
          some `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena do
        return false
      let realizationConst <- mkConstWithFreshMVarLevels realizationName
      let realizationType <- instantiateMVars (← whnfR (← inferType realizationConst))
      unless realizationType.getAppFn.constName? ==
          some `D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization do
        return false
      let legacyArgs := realizationType.getAppArgs
      unless legacyArgs.size == 3 do
        return false
      unless ← isDefEq legacyArgs[0]! arenaExpr do
        return false
      unless ← isDefEq legacyArgs[1]! theoremType do
        return false
      let typedRealization := legacyArgs[2]!
      let typedRealizationType <- instantiateMVars (← whnfR (← inferType typedRealization))
      unless typedRealizationType.getAppFn.constName? ==
          some `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization do
        return false
      let realizationArgs := typedRealizationType.getAppArgs
      unless realizationArgs.size == 2 do
        return false
      let arenaValue <- mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena
        #[arenaExpr]
      let stateType <- mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.Arena.State #[arenaValue]
      let stateDecidableEq <- mkAppM
        `D5.S3.ConceptDynamics.InformationEscape.Arena.stateDecidableEq #[arenaValue]
      let compiler <- mkConstWithFreshMVarLevels
        `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization.toPrimitiveBundle
      let compiledBundle := mkAppN compiler
        #[stateType, realizationArgs[1]!, stateDecidableEq, typedRealization]
      let suppliedBundle <- elabTerm primitiveTerm none
      synthesizeSyntheticMVarsNoPostponing
      return ← isDefEq suppliedBundle compiledBundle
    catch _ =>
      return false
  unless valid do
    throwError "IE-C006 StatementProofMismatch: {theoremName}"

elab "information_theorem " theoremId:ident ppLine
    "in " arenaId:ident ppLine
    "primitives " primitives:term ppLine
    ": " statement:term " := " proof:term : command => do
    let theoremName <- declarationName theoremId
    ensureRegisterableName (← getEnv) theoremName
    let _ <- try
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo arenaId
    catch _ =>
      throwErrorAt arenaId "IE-C003 ArenaResolutionFailed: {arenaId.getId}"
    elabCommand (← `(command| theorem $theoremId : $statement := $proof))
    let unitName := theoremName.str theoremUnitSuffix
    let unitId := absoluteIdentFrom theoremId unitName
    elabCommand (← `(command| def $unitId :
        D5.S3.ConceptDynamics.InformationEscape.TheoremUnit ($arenaId:ident).toArena :=
      { primitives := $primitives
        Statement := $statement
        proof := $theoremId }))
    registerEntry {
      theoremName
      unitName
      arenaName := (← liftCoreM <| realizeGlobalConstNoOverloadWithInfo arenaId)
      realizationName := .anonymous
    }

syntax (name := registerInformationTheoremCmd)
  "register_information_theorem " ident ppLine
    "in " ident ppLine
    "primitives " term " realization " ident : command

@[command_elab registerInformationTheoremCmd]
private def elabRegisterInformationTheorem : CommandElab := fun stx => do
    let theoremId : TSyntax `ident := ⟨stx[1]⟩
    let arenaId : TSyntax `ident := ⟨stx[3]⟩
    let primitiveTerm : TSyntax `term := ⟨stx[5]⟩
    let realizationId : TSyntax `ident := ⟨stx[7]⟩
    let theoremName <- resolveTheorem theoremId
    ensureRegisterableName (← getEnv) theoremName
    let arenaName <- try
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo arenaId
    catch _ =>
      throwErrorAt arenaId "IE-C003 ArenaResolutionFailed: {arenaId.getId}"
    let realizationName <- try
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo realizationId
    catch _ =>
      throwError "IE-C006 StatementProofMismatch: {theoremName}"
    checkLegacyBinding theoremName arenaName realizationName primitiveTerm
    let unitName := theoremName.str theoremUnitSuffix
    let unitId := absoluteIdentFrom theoremId unitName
    let unitType <- `(term|
      D5.S3.ConceptDynamics.InformationEscape.TheoremUnit ($arenaId:ident).toArena)
    let unitValue <- `(term|
      D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit
        $realizationId:ident $theoremId:ident)
    elabCommand (← `(command| def $unitId : $unitType := $unitValue))
    registerEntry {
      theoremName
      unitName
      arenaName
      realizationName
    }

end LeanInformationAudit

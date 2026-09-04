import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Lean

namespace LeanInformationAudit

open Lean
open Lean.Meta

private def theoremUnitName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit

private def primitiveLawArenaName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena

structure InformationRegistryEntry where
  theoremName : Name
  unitName : Name
  arenaName : Name
  /-- `realizationName = Name.anonymous` iff the unit is native. This deviation
  from the spec section 25.1 three-field entry is required by the realization
  validation in sections 24.2, 24.4, and 26.4. -/
  realizationName : Name

initialize informationRegistryExt :
    SimplePersistentEnvExtension InformationRegistryEntry
      (Array InformationRegistryEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun ess => ess.foldl (· ++ ·) #[]
  }

def InformationRegistry.entries (env : Environment) :
    Array InformationRegistryEntry :=
  informationRegistryExt.getState env

def InformationRegistry.find? (env : Environment) (theoremName : Name) :
    Option InformationRegistryEntry :=
  (entries env).find? fun entry => entry.theoremName == theoremName

def InformationRegistry.hasTheorem (env : Environment) (n : Name) : Bool :=
  (find? env n).isSome

def InformationRegistry.hasUnit (env : Environment) (n : Name) : Bool :=
  (entries env).any fun entry => entry.unitName == n

def isCompanionName : Name -> Bool
  | .str _ suffix =>
      suffix == "__lowers_escape" ||
        suffix == "__escape_enriched" ||
        suffix == "__information_unit" ||
        suffix == "__primitive_realization"
  | _ => false

private def duplicateError (name : Name) : String :=
  s!"IE-C002 DuplicateRegistration: {name}"

private def statementMismatchError (name : Name) : String :=
  s!"IE-C006 StatementProofMismatch: {name}"

/-- Perform the environment-only portion of registry integrity validation.

The command layer follows this with `validateEntryTypes`, whose metavariable
instantiation and reducible weak-head normalization require `MetaM`. -/
def validateEntry (env : Environment) (entry : InformationRegistryEntry) :
    Except String Unit := do
  if isCompanionName entry.theoremName then
    throw s!"IE-C011 GeneratedCertificateRegistered: {entry.theoremName}"
  match env.find? entry.theoremName with
  | some (.thmInfo _) => pure ()
  | _ => throw s!"IE-C001 UnregisteredTheoremUnit: {entry.theoremName}"
  unless env.contains entry.unitName do
    throw (statementMismatchError entry.theoremName)
  unless env.contains entry.arenaName do
    throw s!"IE-C003 ArenaResolutionFailed: {entry.arenaName}"
  if InformationRegistry.hasTheorem env entry.theoremName then
    throw (duplicateError entry.theoremName)
  if InformationRegistry.hasUnit env entry.unitName then
    throw (duplicateError entry.unitName)
  let unitInfo := env.find? entry.unitName |>.get!
  unless unitInfo.type.getAppFn.constName? == some theoremUnitName do
    throw (statementMismatchError entry.theoremName)

/-- Complete §25.4 validation using kernel definitional equality.

The exact cheap check instantiates metavariables, applies reducible WHNF to the
registered theorem type, `unit.Statement`, and the inferred type of
`unit.proof`, then asks the kernel's definitional equality procedure to compare
both projection types with the theorem type. -/
def validateEntryTypes (env : Environment) (entry : InformationRegistryEntry) :
    MetaM (Except String Unit) := do
  match validateEntry env entry with
  | .error message => return .error message
  | .ok () => pure ()
  try
    let theoremExpr <- mkConstWithFreshMVarLevels entry.theoremName
    let theoremType <- instantiateMVars (← whnfR (← inferType theoremExpr))
    let unitExpr <- mkConstWithFreshMVarLevels entry.unitName
    let unitType <- instantiateMVars (← whnfR (← inferType unitExpr))
    unless unitType.getAppFn.constName? == some theoremUnitName do
      return .error (statementMismatchError entry.theoremName)
    let unitArgs := unitType.getAppArgs
    if unitArgs.isEmpty then
      return .error (statementMismatchError entry.theoremName)
    let arenaExpr <- mkConstWithFreshMVarLevels entry.arenaName
    let arenaType <- instantiateMVars (← whnfR (← inferType arenaExpr))
    unless arenaType.getAppFn.constName? == some primitiveLawArenaName do
      return .error s!"IE-C003 ArenaResolutionFailed: {entry.arenaName}"
    let expectedArena <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena
      #[arenaExpr]
    unless ← isDefEq unitArgs.back! expectedArena do
      return .error (statementMismatchError entry.theoremName)
    let statementExpr <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.Statement
      #[unitExpr]
    let statementType <- instantiateMVars (← whnfR statementExpr)
    let proofExpr <- mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.proof
      #[unitExpr]
    let proofType <- instantiateMVars (← whnfR (← inferType proofExpr))
    unless ← isDefEq statementType theoremType do
      return .error (statementMismatchError entry.theoremName)
    unless ← isDefEq proofType theoremType do
      return .error (statementMismatchError entry.theoremName)
    return .ok ()
  catch _ =>
    return .error (statementMismatchError entry.theoremName)

end LeanInformationAudit

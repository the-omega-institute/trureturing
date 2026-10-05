import LeanInformationAudit.InputTypes
import LeanInformationAudit.SnapshotTypes

namespace LeanInformationAudit
open Lean


namespace TemplateBinding

structure ResolvedDeclaration where
  theoremName : Name
  arena : Name
  descriptor : Option Expr
  sourceRecord : Option Name := none
  diagnostic : Option String := none
  escapeInput : EscapeRecordInput := {}

end TemplateBinding

/-- Resolved and elaborated source input. No assessment result is stored. -/
structure RegistrationInput where
  entry : InformationRegistryEntry
  sourceText : String
  options : Options
  suppliedPrimitives : Option Expr := none
  viaDescriptor : Option Expr := none
  outputEvidence : Option Expr := none
  /-- Author-supplied bridge before an occurrence companion aliases it. -/
  realizationSource : Option Name := none
  declaration : Option TemplateBinding.ResolvedDeclaration := none

structure TemplateEnrollmentInput where
  owner : Name
  name : Name
  version : Nat
  constructors : Array Name
  sourceText : String
  options : Options

structure CompiledSealCatalog where
  source : Name
  arenaName : Name
  catalogId : Name
  value : Expr

structure SealInput where
  rootId : Name
  catalogs : Array CompiledSealCatalog := #[]
  options : Options

private initialize assessmentCatalogs : EnvExtension (Array RootCatalogContract) ←
  registerEnvExtension (pure #[])

namespace RootCatalogs
def find? (env : Environment) (rootId : Name) : Option RootCatalogContract :=
  (assessmentCatalogs.getState env).find? (·.rootId == rootId)

/-- Install decoded catalogs for this target assessment only. -/
def install (env : Environment) (contracts : Array RootCatalogContract) : Environment :=
  assessmentCatalogs.setState env contracts
end RootCatalogs

structure ExpectedOccurrence where
  rootId : Name
  objectArenaName : Name
  theoremName : Name
  statementIdentity : String := ""
  capturedStatement : Option Expr := none
  registrationModuleName : Name
  deriving Inhabited, Repr

def theoremUnitSuffix := "__information_unit"
def primitiveRealizationSuffix := "__primitive_realization"
def arenaConstructionMarker : Name := `LeanInformationAudit.arenaConstruction

def catalogQualifiedName (rootId objectArenaName : Name) (catalogId : CatalogId)
    (theoremName : Name) (suffix : String) : Name :=
  theoremName
    |>.str (rootId.toString ++ "/" ++ objectArenaName.toString ++ "/" ++ catalogId.toString)
    |>.str suffix

def localCompanionName (env : Environment) (rootId owner : Name) (suffix : String) : Name :=
  let name := owner.str suffix
  let declaringModule := (env.getModuleIdxFor? owner).map fun index =>
    env.header.moduleNames[index.toNat]!
  if declaringModule.getD env.header.mainModule == rootId then name
  else match (RootCatalogs.find? env rootId).bind (·.companionPrefix) with
    | some companion => companion ++ name
    | none => mkPrivateNameCore rootId (privateToUserName name)

end LeanInformationAudit


namespace LeanInformationAudit.TemplateBinding
open Lean

private initialize pendingDeclaration : EnvExtension (Option ResolvedDeclaration) ←
  registerEnvExtension (pure none)

def withDeclaration (declaration : ResolvedDeclaration)
    (action : Elab.Command.CommandElabM Unit) : Elab.Command.CommandElabM Unit := do
  let previous := pendingDeclaration.getState (← getEnv)
  if previous.isSome then throwError "unclassified_form:dtr.nested_declaration"
  modifyEnv (pendingDeclaration.setState · (some declaration))
  try action finally modifyEnv (pendingDeclaration.setState · previous)

def currentDeclaration (env : Environment) : Option ResolvedDeclaration :=
  pendingDeclaration.getState env

end LeanInformationAudit.TemplateBinding

namespace LeanInformationAudit.RegistrationElaboration
open Lean Meta

def witnessArenaName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessArena

def objectDomainArenaName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena

def witnessBridgeName : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessPrimitiveRealization

/-- Keep the author's arena for ownership and bridge identity. Only the derived
law arena and its finite carrier are used for signature and catalog checks. -/
structure NormalizedArena where
  original : Expr
  law : Expr
  finite : Expr
  witness : Bool
  domain : Option Expr

def normalizeArena (arena : Expr) : MetaM NormalizedArena := do
  let type ← whnfR (← inferType arena)
  let witness := type.isConstOf witnessArenaName
  let objectDomain := type.isConstOf objectDomainArenaName
  let law ← if witness then mkAppM (witnessArenaName.str "toPrimitiveLawArena") #[arena]
    else if objectDomain then mkAppM (objectDomainArenaName.str "toPrimitiveLawArena") #[arena]
    else pure arena
  let finite ← if witness || type.isConstOf `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena then
      mkAppM `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena #[law]
    else if objectDomain then mkAppM `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena #[law]
    else if type.isConstOf `D5.S3.ConceptDynamics.InformationEscape.Arena then pure arena
    else throwError "IE-C003 ArenaResolutionFailed: {arena}"
  let domain ← if objectDomain then
      some <$> mkAppM (objectDomainArenaName.str "Domain") #[arena]
    else pure none
  return { original := arena, law, finite, witness, domain }

end LeanInformationAudit.RegistrationElaboration

namespace LeanInformationAudit
open Lean Elab Command

/-- Roll back the complete assessment environment when a command fails. -/
def registrationTransaction (action : CommandElabM Unit) : CommandElabM Unit := do
  let saved ← getEnv
  try action catch error =>
    setEnv saved
    throw error
end LeanInformationAudit

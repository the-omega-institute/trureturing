import LeanInformationAuditInterface.Records
import LeanInformationAuditInterface.RootContract

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
  declaration : Option TemplateBinding.ResolvedDeclaration := none

structure TemplateEnrollmentInput where
  owner : Name
  name : Name
  version : Nat
  constructors : Array Name
  sourceText : String
  options : Options

structure SealInput where
  rootId : Name
  options : Options

private initialize registrationInputs :
    SimplePersistentEnvExtension RegistrationInput (Array RegistrationInput) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }
private initialize templateInputs :
    SimplePersistentEnvExtension TemplateEnrollmentInput (Array TemplateEnrollmentInput) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }
private initialize sealInputs :
    SimplePersistentEnvExtension SealInput (Array SealInput) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

namespace RegistrationInputs
def add (env : Environment) (input : RegistrationInput) : Environment :=
  registrationInputs.addEntry env input
def owned (env : Environment) : Array (Name × RegistrationInput) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    for input in registrationInputs.getModuleEntries env index do
      result := result.push (env.header.moduleNames[index]!, input)
  for input in (registrationInputs.getEntries env).reverse do
    result := result.push (env.header.mainModule, input)
  return result
end RegistrationInputs

namespace TemplateEnrollmentInputs
def add (env : Environment) (input : TemplateEnrollmentInput) : Environment :=
  templateInputs.addEntry env input
def owned (env : Environment) : Array (Name × TemplateEnrollmentInput) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    for input in templateInputs.getModuleEntries env index do
      result := result.push (env.header.moduleNames[index]!, input)
  for input in (templateInputs.getEntries env).reverse do
    result := result.push (env.header.mainModule, input)
  return result
end TemplateEnrollmentInputs

namespace SealInputs
def add (env : Environment) (input : SealInput) : Environment := sealInputs.addEntry env input
def owned (env : Environment) : Array (Name × SealInput) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    for input in sealInputs.getModuleEntries env index do
      result := result.push (env.header.moduleNames[index]!, input)
  for input in (sealInputs.getEntries env).reverse do
    result := result.push (env.header.mainModule, input)
  return result
end SealInputs

private initialize rootCatalogInputs :
    SimplePersistentEnvExtension RootCatalogContract (Array RootCatalogContract) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

namespace RootCatalogs
def find? (env : Environment) (rootId : Name) : Option RootCatalogContract :=
  (rootCatalogInputs.getState env).find? (·.rootId == rootId)
def owned (env : Environment) : Array (Name × RootCatalogContract) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    for input in rootCatalogInputs.getModuleEntries env index do
      result := result.push (env.header.moduleNames[index]!, input)
  for input in (rootCatalogInputs.getEntries env).reverse do
    result := result.push (env.header.mainModule, input)
  return result
def declare (contract : RootCatalogContract) : Elab.Command.CommandElabM Unit :=
  modifyEnv fun env =>
    let env := match contract.companionPrefix with
      | some companion => env.registerNamespace companion
      | none => env
    rootCatalogInputs.addEntry env contract
end RootCatalogs

structure ExpectedOccurrence where
  rootId : Name
  objectArenaName : Name
  theoremName : Name
  statementIdentity : String := ""
  capturedStatement : Option Expr := none
  registrationModuleName : Name
  deriving Inhabited, Repr

private initialize expectedOccurrenceInputs :
    SimplePersistentEnvExtension ExpectedOccurrence (Array ExpectedOccurrence) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push, addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }

namespace ExpectedOccurrenceManifest
def declaredEntries (env : Environment) (rootId : Name) : Array ExpectedOccurrence :=
  (expectedOccurrenceInputs.getState env).filter (·.rootId == rootId)
def owned (env : Environment) : Array (Name × ExpectedOccurrence) := Id.run do
  let mut result := #[]
  for index in [:env.header.moduleNames.size] do
    for input in expectedOccurrenceInputs.getModuleEntries env index do
      result := result.push (env.header.moduleNames[index]!, input)
  for input in (expectedOccurrenceInputs.getEntries env).reverse do
    result := result.push (env.header.mainModule, input)
  return result
def addEntry (env : Environment) (entry : ExpectedOccurrence) : Environment :=
  expectedOccurrenceInputs.addEntry env entry
end ExpectedOccurrenceManifest

def theoremUnitSuffix := "__information_unit"
def primitiveRealizationSuffix := "__primitive_realization"
def arenaConstructionMarker : Name := `LeanInformationAudit.arenaConstruction

def generatedCompanionSuffixes : Array String := #[
  theoremUnitSuffix,
  primitiveRealizationSuffix,
  "__lowers_escape",
  "__trivial_in_catalog",
  "__escape_enriched",
  "__information_catalog",
  "__catalog_irredundant",
  "__catalog_redundant",
  "__system_catalog_irredundant",
  "__system_catalog_not_irredundant",
  "__information_registration_diagnostic"
]

def isCompanionName : Name -> Bool
  | .str _ suffix =>
      -- Every reserved suffix starts with "__". Ordinary names avoid the
      -- interpreted array scan; the registry remains the suffix authority.
      suffix.startsWith "__" && generatedCompanionSuffixes.contains suffix
  | _ => false

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

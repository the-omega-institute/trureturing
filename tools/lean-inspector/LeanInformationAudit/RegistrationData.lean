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

/-- Judge-owned output names. The report rejects a registration of one of
these companions (IE-C011). -/
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

end LeanInformationAudit

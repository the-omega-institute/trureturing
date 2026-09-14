import Lean

/- Persistent entry types shared by their producers and the olean reader.
No evidence values or project Environment are imported here. -/
namespace LeanInformationAudit

open Lean

abbrev CatalogId := Name

namespace TemplateAudit

inductive Origin where
  | templateBody | suppliedArgument | actualExtraction | proofLeaf
  deriving BEq, Inhabited, Repr

inductive SlotKind where
  | carrier | data | function | predicate | dictionary | proof | interface
  deriving BEq, Inhabited, Repr

/-- Raw syntax is retained at proof and supplied-argument boundaries. Neither
boundary grants normalization or permits walking a proof implementation. -/
inductive PlanNode where
  | atom (raw : Expr)
  | app (fn arg : PlanNode)
  | lam (domain body : PlanNode) (binderInfo : BinderInfo)
  | forallE (domain body : PlanNode) (binderInfo : BinderInfo)
  | letE (type value body : PlanNode) (nondep : Bool)
  | mdata (data : MData) (body : PlanNode)
  | proj (typeName : Name) (index : Nat) (body : PlanNode)
  | expanded (raw : Expr) (checked : PlanNode)
  | supplied (raw : Expr)
  | proofLeaf (type raw : Expr)
  deriving Inhabited

structure DependencyIdentity where
  name : Name
  owner : Name
  typeIdentity : String
  bodyIdentity : String
  deriving Inhabited

structure SourceInput where
  path : String
  sha256 : String
  deriving BEq, Inhabited

structure Slot where
  kind : SlotKind
  binderInfo : BinderInfo
  type : Expr
  deriving Inhabited

/-- Serialized data, not an enrollment authority. Only the private producer
extension in Registry accepts a result of its checked-plan constructor. -/
structure TemplatePlanData where
  schemaVersion : Nat := 1
  grammarVersion : Nat := 1
  constructorRecursionVersion : Nat := 1
  compatibilityVersion : Nat := 4
  compiler : String
  toolchain : String
  policyIdentity : String
  sourceInputs : Array SourceInput
  name : Name
  definitionOwner : Name
  enrollmentOwner : Name
  levelParams : List Name
  slots : Array Slot
  typeIdentity : String
  bodyIdentity : String
  planIdentity : String
  dependencies : Array DependencyIdentity
  plan : PlanNode
  typePlan : PlanNode
  rules : Array String
  chargedWork : Nat
  serializedBytes : Nat
  deriving Inhabited

end TemplateAudit

structure TemplateOccurrenceKey where
  root : Name
  registrationModule : Name
  theoremName : Name
  objectArena : Name
  catalog : Name
  deriving BEq, Hashable, Inhabited

structure TemplateOccurrenceEvent where
  key : TemplateOccurrenceKey
  unitName : Name
  realizationName : Name
  statement : Expr
  levelParams : List Name
  statementIdentity : String
  arena : Expr
  registrationSource : String
  registrationSourceIdentity : String
  deriving Inhabited

structure TemplateBindingCertificate where
  evidenceRef : String
  key : TemplateOccurrenceKey
  planIdentity : String
  descriptorIdentity : String
  actualIdentity : String
  argumentInputs : Array TemplateAudit.DependencyIdentity
  extractionInputs : Array TemplateAudit.DependencyIdentity
  deriving Inhabited

inductive TemplateBindingResult where
  | undeclared
  | declaredUnresolved (diagnostic : String)
  | declaredValidated (certificate : TemplateBindingCertificate)
  deriving Inhabited

structure BindingRecord where
  schemaVersion : Nat := 1
  compatibilityVersion : Nat := 4
  occurrence : TemplateOccurrenceEvent
  descriptor : Option Expr
  bindingOwner : Option Name
  result : TemplateBindingResult
  deriving Inhabited

structure TemplateBindingClaim where
  key : TemplateOccurrenceKey
  arena : Expr
  descriptor : Expr
  owner : Name
  deriving Inhabited

inductive CatalogKind where
  | canonicalMaximal
  | analysisView
  deriving BEq, Inhabited, Repr

def CatalogKind.artifactName : CatalogKind -> String
  | .canonicalMaximal => "canonical_maximal"
  | .analysisView => "analysis_view"

/-- Occurrence-bound inputs to the executable predicates in RegistrationReifier.
No stored boolean asserts certification; consumers revalidate these inputs. -/
structure AutoDerivedSemanticCertificate where
  occurrence : Array Name
  catalogKind : CatalogKind
  localRegistrationNames : Bool
  statementIdentity : String
  levelParams : List Name
  statement : Expr
  descriptor : Expr
  arena : Expr
  nondegenerate : Name
  outputEvidence : Expr

structure InformationRegistryEntry where
  theoremName : Name
  unitName : Name
  /-- The `PrimitiveLawArena` presentation. -/
  arenaName : Name
  /-- The declaration holding the native realization or the legacy witness. -/
  realizationName : Name
  variationWitness : Name := .anonymous
  sensitivityWitness : Name := .anonymous
  catalogId : CatalogId := .anonymous
  catalogKind : CatalogKind := .canonicalMaximal
  registrationModuleName : Name := .anonymous
  objectArenaName : Name := .anonymous
  /-- Resolved declaration owner; arenaName/objectArenaName retain the source spelling. -/
  resolvedArenaName : Name := .anonymous
  /-- Stable identity of the elaborated theorem statement captured at registration. -/
  statementIdentity : String := ""
  /-- False exactly for registrations using occurrence-aware syntax. -/
  localRegistrationNames : Bool := true
  derivedCertificate : Option AutoDerivedSemanticCertificate := none

def InformationRegistryEntry.canonicalObjectArenaName
    (entry : InformationRegistryEntry) : Name :=
  if !entry.resolvedArenaName.isAnonymous then entry.resolvedArenaName
  else if entry.objectArenaName.isAnonymous then entry.arenaName else entry.objectArenaName

def InformationRegistryEntry.effectiveCatalogId
    (entry : InformationRegistryEntry) : CatalogId :=
  if entry.catalogId.isAnonymous then entry.canonicalObjectArenaName else entry.catalogId

/-- A closed catalog and the canonical theorem-to-index assignment used by the seal. -/
structure CatalogUnitRecord where
  theoremName : Name
  unitName : Name
  realizationName : Name
  registrationModuleName : Name
  index : Nat
  deriving Inhabited

structure CatalogRecord where
  rootId : Name
  catalogId : CatalogId
  catalogKind : CatalogKind
  arenaName : Name
  catalogName : Name
  units : Array CatalogUnitRecord
  localSealNames : Bool
  deriving Inhabited

inductive OccurrenceCertificate where
  | positive (name : Name)
  | trivial (name : Name)
  deriving Inhabited, Repr

def OccurrenceCertificate.name : OccurrenceCertificate → Name
  | .positive name | .trivial name => name

def OccurrenceCertificate.suffix : OccurrenceCertificate → String
  | .positive _ => "__lowers_escape"
  | .trivial _ => "__trivial_in_catalog"

inductive CatalogVerdict where
  | irredundant (name : Name)
  | redundant (name : Name)
  deriving Inhabited, Repr

def CatalogVerdict.name : CatalogVerdict → Name
  | .irredundant name | .redundant name => name

def CatalogVerdict.label : CatalogVerdict → String
  | .irredundant _ => "irredundant"
  | .redundant _ => "redundant"

def CatalogVerdict.suffix : CatalogVerdict → String
  | .irredundant _ => "__catalog_irredundant"
  | .redundant _ => "__catalog_redundant"

/-- Context-specific evidence for the single IE-C007 record. -/
inductive ZeroCaptureContext where
  | finite (full without : Nat) (stateEnumeration : Name)
  | structural (registration catalogSeal : Name)
  deriving Inhabited

structure ZeroCaptureRecord where
  root : Name
  theoremName : Name
  arena : Name
  catalog : Name
  index : Nat
  realization : Name
  trivialityCertificate : Name
  context : ZeroCaptureContext
  sameKernelCandidates : Array (Name × Nat × Name) := #[]
  closureCandidates : Array Name := #[]
  closureCertificate : Option Name := none
  deriving Inhabited

/-- Computed theorem data retained for summaries and the optional artifact. -/
structure SealTheoremRecord where
  theoremName : Name
  unitName : Name
  realizationName : Name
  certificate : OccurrenceCertificate
  closureCertificate : Option Name := none
  registrationModuleName : Name
  index : Nat
  primitiveCount : Nat
  primitiveAxes : Array String
  primitiveKernelAddress : String
  uniqueCaptureCount : Nat
  fullEscapeCount : Nat
  withoutEscapeCount : Nat
  roleSignatureHistogram : Array (String × Nat)
  proofMethod : String

deriving instance Inhabited for SealTheoremRecord

def SealTheoremRecord.certificateName (row : SealTheoremRecord) : Name := row.certificate.name

/-- Computed arena data retained for summaries and the optional artifact. -/
structure SealArenaRecord where
  catalog : CatalogRecord
  verdict : CatalogVerdict
  collisionClasses : Array (Array Name × Array Name) := #[]
  stateEnumeration : Option Name := none
  proofMethod : String
  stateCard : Nat
  offDiagonalPairCount : Nat
  fullEscapeCount : Nat
  theorems : Array SealTheoremRecord
  deriving Inhabited

namespace DispositionCensus

/-- Provenance details, retained without proposition normalization. This mutable
registry is not write authority: provenance means generated by structural_theorem
in source, checked by parsing that immutable input. Source rewriting during a
build and modified source search paths are outside the contract. The section
23.6 payload types remain unchanged. -/
structure StructuralProvenanceEntry where
  theoremName : Name
  lawArenaConst : Name
  realizationConst : Name
  unitConst : Name
  statementExpr : Expr
  proofExpr : Expr
  levelParams : List Name
  certificateName : Name
  sensitivityWitness : Name := .anonymous
  domainName : Name := .anonymous
  registrationModule : Name
  canonicalArena : Name
  lawArenaSyntax : String := ""
  realizationSyntax : String := ""
  deriving Inhabited


end DispositionCensus
end LeanInformationAudit

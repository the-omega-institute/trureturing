import Lean

namespace LeanInformationAudit
open Lean

abbrev CatalogId := Name

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

/-- Syntax input is retained for authoritative reassessment, never executed. -/
structure EscapeRecordInput where
  fromObject : Option Expr := none
  continuation : Option Expr := none
  openContinuation : Bool := false
  deriving Inhabited, BEq

structure EscapeFromIdentity where
  name : Name
  typeIdentity : String
  objectIdentity : String
  deriving Inhabited, BEq

structure EscapeContinuationIdentity where
  kind : String
  declarationName : Option Name := none
  statementIdentity : Option String := none
  chainName : Option Name := none
  deriving Inhabited, BEq

structure EscapeRecordEvidence where
  fromObject : Option EscapeFromIdentity := none
  continuation : Option EscapeContinuationIdentity := none
  bridgeKind : String := "legacy"
  deriving Inhabited, BEq

structure TemplateBindingClaim where
  key : TemplateOccurrenceKey
  arena : Expr
  descriptor : Option Expr
  resolutionDiagnostic : Option String := none
  escapeInput : EscapeRecordInput := {}
  owner : Name
  deriving Inhabited

namespace TemplateAudit

structure DependencyIdentity where
  name : Name
  owner : Name
  typeIdentity : String
  bodyIdentity : String
  deriving Inhabited

end TemplateAudit

structure TemplateBindingCertificate where
  evidenceRef : String
  key : TemplateOccurrenceKey
  planIdentity : String
  descriptorIdentity : String
  actualIdentity : String
  argumentInputs : Array TemplateAudit.DependencyIdentity
  extractionInputs : Array TemplateAudit.DependencyIdentity
  escape : EscapeRecordEvidence := {}
  deriving Inhabited

inductive TemplateBindingResult where
  | undeclared
  | declaredUnresolved (diagnostic : String)
  | declaredValidated (certificate : TemplateBindingCertificate)
  deriving Inhabited

structure BindingRecord where
  schemaVersion : Nat := 1
  compatibilityVersion : Nat := 7
  occurrence : TemplateOccurrenceEvent
  descriptor : Option Expr
  bindingOwner : Option Name
  result : TemplateBindingResult
  escape : EscapeRecordEvidence := {}
  deriving Inhabited

inductive CatalogKind where
  | canonicalMaximal
  | analysisView
  deriving BEq, Inhabited, Repr

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

inductive CatalogVerdict where
  | irredundant (name : Name)
  | redundant (name : Name)
  deriving Inhabited, Repr

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

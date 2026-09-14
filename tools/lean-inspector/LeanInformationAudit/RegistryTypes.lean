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
  | typeNode (checked : PlanNode)
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

/- Bounded decoder for the canonical length-prefixed plan payload. The
persistent extension stores bytes, so none of these nodes exist before its
framing and aggregate-budget checks. Allocation debit is conservative and
includes token copies, collection slots and expression/plan constructors. -/
namespace PlanDecoder

private structure State where
  bytes : ByteArray
  offset : Nat := 0
  allocationRemaining : Nat
  levelParams : List Name := []
  deriving Inhabited

private abbrev M := StateT State (Except String)

private def fail {α : Type} : M α := throw "incomplete_closure:E7.import_encoding"

private def allocate (bytes : Nat) : M Unit := do
  unless bytes ≤ (← get).allocationRemaining do
    throw "incomplete_closure:E8.import_allocation"
  modify fun s => { s with allocationRemaining := s.allocationRemaining - bytes }

private def node (depth : Nat) : M Unit := do
  if depth > 256 then throw "incomplete_closure:E8.import_depth"
  allocate 96

private def token : M String := do
  let state ← get
  let mut cursor := state.offset
  let mut length := 0
  let mut digits := 0
  while cursor < state.bytes.size && state.bytes[cursor]! != 58 do
    let c := state.bytes[cursor]!.toNat
    unless 48 ≤ c && c ≤ 57 && digits < 5 do fail
    if digits == 1 && length == 0 then fail
    length := 10 * length + c - 48
    cursor := cursor + 1
    digits := digits + 1
  unless digits > 0 && cursor < state.bytes.size &&
      length ≤ state.bytes.size - (cursor + 1) do fail
  allocate (3 * length + 64)
  let some value := String.fromUTF8? (state.bytes.extract (cursor + 1) (cursor + 1 + length)) | fail
  modify fun s => { s with offset := cursor + 1 + length }
  return value

private def expect (text : String) : M Unit := do
  unless (← token) == text do fail

private def natural (bound : Nat := 65536) : M Nat := do
  let text ← token
  let some n := text.toNat? | fail
  unless toString n == text && n ≤ bound do fail
  return n

private def boolean : M Bool := do
  match ← token with
  | "true" => return true
  | "false" => return false
  | _ => fail

private def sequence (bound : Nat) (action : M α) : M (Array α) := do
  let count ← natural bound
  allocate (24 * count + 32)
  let mut values := #[]
  for _ in [:count] do values := values.push (← action)
  return values

private partial def name (depth : Nat := 0) : M Name := do
  node depth
  match ← token with
  | "anonymous" => return .anonymous
  | "str" => return .str (← name (depth + 1)) (← token)
  | "num" => return .num (← name (depth + 1)) (← natural)
  | _ => fail

private partial def level (depth : Nat := 0) : M Level := do
  node depth
  match ← token with
  | "zero" => return .zero
  | "succ" => return .succ (← level (depth + 1))
  | "max" => return .max (← level (depth + 1)) (← level (depth + 1))
  | "imax" => return .imax (← level (depth + 1)) (← level (depth + 1))
  | "parameter" =>
    let index ← natural
    let some param := (← get).levelParams[index]? | fail
    return .param param
  | "rigid" =>
    let value ← name
    if (← get).levelParams.contains value then fail
    return .param value
  | _ => fail

private def substring : M Substring.Raw := do
  let str ← token
  let start ← natural str.utf8ByteSize
  let stop ← natural str.utf8ByteSize
  unless start ≤ stop do fail
  return ⟨str, ⟨start⟩, ⟨stop⟩⟩

private def source : M SourceInfo := do
  match ← token with
  | "none" => return .none
  | "synthetic" => return .synthetic ⟨← natural⟩ ⟨← natural⟩ (← boolean)
  | "original" => return .original (← substring) ⟨← natural⟩ (← substring) ⟨← natural⟩
  | _ => fail

private def preresolved : M Syntax.Preresolved := do
  node 0
  match ← token with
  | "namespace" => return .namespace (← name)
  | "decl" => return .decl (← name) (← sequence 65536 token).toList
  | _ => fail

private partial def readSyntax (depth : Nat := 0) : M Syntax := do
  node depth
  match ← token with
  | "missing" => return .missing
  | "atom" => return .atom (← source) (← token)
  | "node" => return .node (← source) (← name) (← sequence 65536 (readSyntax (depth + 1)))
  | "ident" => return .ident (← source) (← substring) (← name) (← sequence 65536 preresolved).toList
  | _ => fail

private def dataValue (depth : Nat) : M DataValue := do
  node depth
  match ← token with
  | "string" => return .ofString (← token)
  | "bool" => return .ofBool (← boolean)
  | "name" => return .ofName (← name)
  | "nat" =>
    let text ← token
    let some n := text.toNat? | fail
    unless toString n == text do fail
    return .ofNat n
  | "int" =>
    let text ← token
    let some n := text.toInt? | fail
    unless toString n == text do fail
    return .ofInt n
  | "syntax" => return .ofSyntax (← readSyntax depth)
  | _ => fail

private def binderInfo : M BinderInfo := do
  let text ← token
  for value in #[BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
    if reprStr value == text then return value
  fail

private partial def expr (depth : Nat := 0) : M Expr := do
  node depth
  let child := expr (depth + 1)
  match ← token with
  | "bvar" => return .bvar (← natural)
  | "sort" => return .sort (← level)
  | "const" => return .const (← name) (← sequence 64 level).toList
  | "app" => return .app (← child) (← child)
  | "lambda" =>
    let bi ← binderInfo
    return .lam .anonymous (← child) (← child) bi
  | "forall" =>
    let bi ← binderInfo
    return .forallE .anonymous (← child) (← child) bi
  | "let" =>
    let nd ← boolean
    return .letE .anonymous (← child) (← child) (← child) nd
  | "natLiteral" =>
    let text ← token
    let some n := text.toNat? | fail
    unless toString n == text do fail
    return .lit (.natVal n)
  | "stringLiteral" => return .lit (.strVal (← token))
  | "metadata" =>
    let entries ← sequence 65536 do return (← name, ← dataValue (depth + 1))
    return .mdata ⟨entries.toList⟩ (← child)
  | "projection" => return .proj (← name) (← natural) (← child)
  | _ => fail

private partial def plan (depth : Nat := 0) : M PlanNode := do
  node depth
  let child := plan (depth + 1)
  let raw := expr (depth + 1)
  match ← token with
  | "body" => return .atom (← raw)
  | "expanded" => return .expanded (← raw) (← child)
  | "proof-leaf" => return .proofLeaf (← raw) (← raw)
  | "type-node" => return .typeNode (← child)
  | "application" => return .app (← child) (← child)
  | "lambda" =>
    let bi ← binderInfo
    return .lam (← child) (← child) bi
  | "forall" =>
    let bi ← binderInfo
    return .forallE (← child) (← child) bi
  | "let" =>
    let nd ← boolean
    return .letE (← child) (← child) (← child) nd
  | "metadata" =>
    let .mdata m (.bvar 0) ← raw | fail
    return .mdata m (← child)
  | "projection" => return .proj (← name) (← natural) (← child)
  | _ => fail

private def slotKind : M SlotKind := do
  let text ← token
  for kind in #[SlotKind.carrier, .data, .function, .predicate, .dictionary, .proof, .interface] do
    if reprStr kind == text then return kind
  fail

private def digest : M String := do
  let value ← token
  unless value.utf8ByteSize == 64 && value.all (fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) do fail
  return value

private def payload : M TemplatePlanData := do
  expect "DTR-checked-plan-v1"
  for version in #[1, 1, 1, 4] do unless (← natural) == version do fail
  let compiler ← token
  let toolchain ← token
  let policyIdentity ← digest
  let templateName ← name
  let definitionOwner ← name
  let enrollmentOwner ← name
  let levelCount ← natural 64
  allocate (64 * levelCount + 512)
  let levelParams := (List.range levelCount).map (Name.num `_dtr_level)
  modify fun s => { s with levelParams }
  let typeIdentity ← digest
  let bodyIdentity ← digest
  let slots ← sequence 64 do
    let kind ← slotKind
    let bi ← binderInfo
    let type ← expr
    return { kind, binderInfo := bi, type : Slot }
  let dependencies ← sequence 4096 do
    let n ← name
    let owner ← name
    let typeIdentity ← digest
    let bodyIdentity ← token
    unless bodyIdentity.isEmpty || (bodyIdentity.utf8ByteSize == 64 &&
        bodyIdentity.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f'))) do fail
    return { name := n, owner, typeIdentity, bodyIdentity : DependencyIdentity }
  let sourceInputs ← sequence 4096 do
    let path ← token
    let sha256 ← digest
    return { path, sha256 : SourceInput }
  let rules ← sequence 4096 token
  let work ← token
  let some chargedWork := work.toNat? | fail
  unless work.utf8ByteSize == 6 && work.all Char.isDigit && chargedWork ≤ 524288 do fail
  let typePlan ← plan
  let bodyPlan ← plan
  return {
    compiler, toolchain, policyIdentity, sourceInputs, name := templateName,
    definitionOwner, enrollmentOwner, levelParams, slots, typeIdentity, bodyIdentity,
    dependencies, plan := bodyPlan, typePlan, rules, chargedWork, planIdentity := "", serializedBytes := 0 }

/-- Pure decoding cannot confer enrollment authority. The private persistent
extension checks frame identity and actual imported ownership around this call. -/
def decode (bytes : ByteArray) (allocationBudget : Nat) : Except String (TemplatePlanData × Nat) := do
  if bytes.size == 0 || bytes.size > 65536 then throw "incomplete_closure:E8.import_framing"
  let limit := min allocationBudget (32 * bytes.size)
  let (value, state) ← payload.run { bytes, allocationRemaining := limit }
  unless state.offset == bytes.size do throw "incomplete_closure:E7.import_encoding"
  return ({ value with serializedBytes := bytes.size }, limit - state.allocationRemaining)

end PlanDecoder

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
  descriptor : Option Expr
  resolutionDiagnostic : Option String := none
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

namespace LeanInformationAudit
open Lean

/-- Judge-owned semantic API for the lightweight standalone report driver.
The inspector resolves one exact declaration/owner of this type. Content does
not register producers, callbacks, policies or acceptance bits. -/
abbrev InformationTemplateReportDriver := Array Name → MetaM (Array Json)

end LeanInformationAudit

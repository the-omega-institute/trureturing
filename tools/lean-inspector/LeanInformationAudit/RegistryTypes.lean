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

/-- Data syntax is retained at supplied-argument boundaries. Proof leaves retain
only propositions, never proof implementations. -/
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
  | proofLeaf (type : Expr)
  | typeNode (checked : PlanNode)
  /-- Checked E5 inputs remain obligations even when expansion discards them. -/
  | audit (input body : PlanNode)
  deriving Inhabited

/- Construction is bounded independently of typing. A step is charged before
visiting or allocating a node; binder cutoffs are not traversal depths. Cached
Expr flags permit immutable no-op reuse, never an uncharged transformation. -/
/-- Compiler-owned typing placeholder; never a delivered kernel proof. -/
def proofPlaceholder (type : Expr) : Expr := mkApp (mkConst ``lcProof) type

namespace PlanTransform

private abbrev WorkM := StateT Nat (Except String)

private def step (depth : Nat) : WorkM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.construction_depth"
  let remaining ← get
  if remaining == 0 then throw "incomplete_closure:E8.construction_work"
  set (remaining - 1)

private def run (action : WorkM α) (fuel : Nat) : Except String (α × Nat) := do
  let limit := min 524288 fuel
  let (value, remaining) ← action.run limit
  return (value, limit - remaining)

private inductive Operation where
  | lift (amount : Nat)
  | substitute (argument : Expr)
  | abstract (localId : FVarId)
  | universes (parameters : List Name) (values : List Level)

private partial def sameLevel (a b : Level) (depth : Nat) : WorkM Bool := do
  step depth
  match a, b with
  | .zero, .zero => return true
  | .param a, .param b => return a == b
  | .mvar a, .mvar b => return a == b
  | .succ a, .succ b => sameLevel a b (depth + 1)
  | .max a b, .max c d | .imax a b, .imax c d =>
    return (← sameLevel a c (depth + 1)) && (← sameLevel b d (depth + 1))
  | _, _ => return false

private partial def offset (u : Level) (depth : Nat) : WorkM (Level × Nat) := do
  step depth
  match u with
  | .succ v =>
    let (base, amount) ← offset v (depth + 1)
    return (base, amount + 1)
  | _ => return (u, 0)

private partial def neverZero (u : Level) (depth : Nat) : WorkM Bool := do
  step depth
  match u with
  | .succ _ => return true
  | .max a b => return (← neverZero a (depth + 1)) || (← neverZero b (depth + 1))
  | .imax _ b => neverZero b (depth + 1)
  | _ => return false

/-- Exactly the cheap universe simplifications performed by Lean's
instantiateLevelParams (mkLevelMax'/mkLevelIMax'), with charged traversals.
This is universe substitution, not term normalization or defeq comparison. -/
private def maxLevel (u v : Level) (depth : Nat) : WorkM Level := do
  step depth
  if ← sameLevel u v depth then return u
  if u.isZero then return v
  if v.isZero then return u
  let (ub, uo) ← offset u depth
  let (vb, vo) ← offset v depth
  let subsumes := fun a b bb bo ao => do
    if bb.isZero && ao ≥ bo then return true
    match a with
    | .max a₁ a₂ => return (← sameLevel b a₁ depth) || (← sameLevel b a₂ depth)
    | _ => return false
  if ← subsumes u v vb vo uo then return u
  if ← subsumes v u ub uo vo then return v
  if ← sameLevel ub vb depth then return if uo ≥ vo then u else v
  return .max u v

private def imaxLevel (u v : Level) (depth : Nat) : WorkM Level := do
  step depth
  if ← neverZero v depth then return ← maxLevel u v depth
  if v.isZero || u.isZero then return v
  if ← sameLevel u v depth then return u
  return .imax u v

private partial def level (u : Level) (parameters : List Name) (values : List Level)
    (depth : Nat) : WorkM Level := do
  step depth
  if !u.hasParam then return u
  let child := fun v => level v parameters values (depth + 1)
  match u with
  | .param name =>
    let rec lookup : List Name → List Level → WorkM Level
      | p :: ps, v :: vs => do
        step depth
        if p == name then return v
        lookup ps vs
      | _, _ => pure u
    lookup parameters values
  | .succ v => return .succ (← child v)
  | .max a b => maxLevel (← child a) (← child b) (depth + 1)
  | .imax a b => imaxLevel (← child a) (← child b) (depth + 1)
  | _ => return u

private partial def raw (operation : Operation) (e : Expr) (cutoff depth : Nat) : WorkM Expr := do
  step depth
  match operation with
  | .lift amount => if amount == 0 || !e.hasLooseBVars then return e
  | .substitute _ => if !e.hasLooseBVars then return e
  | .abstract _ => if !e.hasFVar then return e
  | .universes parameters values =>
    if parameters.isEmpty || values.isEmpty || !e.hasLevelParam then return e
  let child := fun x => raw operation x cutoff (depth + 1)
  let bound := fun x => raw operation x (cutoff + 1) (depth + 1)
  match e with
  | .bvar i =>
    match operation with
    | .lift amount => return .bvar (if i ≥ cutoff then i + amount else i)
    | .substitute argument =>
      if i == cutoff then return ← raw (.lift cutoff) argument 0 (depth + 1)
      return .bvar (if i > cutoff then i - 1 else i)
    | _ => return e
  | .fvar id =>
    match operation with
    | .abstract localId => return if id == localId then .bvar cutoff else e
    | _ => return e
  | .sort u =>
    match operation with
    | .universes parameters values => return .sort (← level u parameters values (depth + 1))
    | _ => return e
  | .const name us =>
    match operation with
    | .universes parameters values =>
      return .const name (← us.mapM fun u => level u parameters values (depth + 1))
    | _ => return e
  | .app f a => return .app (← child f) (← child a)
  | .lam n t b bi => return .lam n (← child t) (← bound b) bi
  | .forallE n t b bi => return .forallE n (← child t) (← bound b) bi
  | .letE n t v b nd => return .letE n (← child t) (← child v) (← bound b) nd
  | .mdata m b => return .mdata m (← child b)
  | .proj n i b => return .proj n i (← child b)
  | _ => return e

private partial def materialize (p : PlanNode) (depth : Nat) : WorkM Expr := do
  step depth
  let child := fun q => materialize q (depth + 1)
  match p with
  | .atom e | .supplied e => return e
  | .proofLeaf type => return proofPlaceholder type
  | .expanded _ p | .typeNode p | .audit _ p => child p
  | .app f a => return .app (← child f) (← child a)
  | .lam t b bi => return .lam .anonymous (← child t) (← child b) bi
  | .forallE t b bi => return .forallE .anonymous (← child t) (← child b) bi
  | .letE t v b nd => return .letE .anonymous (← child t) (← child v) (← child b) nd
  | .mdata m b => return .mdata m (← child b)
  | .proj n i b => return .proj n i (← child b)

private partial def transform (operation : Operation) (replacement : Option PlanNode)
    (p : PlanNode) (cutoff depth : Nat) : WorkM PlanNode := do
  step depth
  let expr := fun e => raw operation e cutoff (depth + 1)
  let child := fun q => transform operation replacement q cutoff (depth + 1)
  let bound := fun q => transform operation replacement q (cutoff + 1) (depth + 1)
  match p with
  | .supplied _ => return p
  | .atom (.bvar i) =>
    if let .substitute _ := operation then
      if i == cutoff then
        let some argument := replacement | throw "incomplete_closure:E8.substitution_origin"
        return ← transform (.lift cutoff) none argument 0 (depth + 1)
    return .atom (← expr (.bvar i))
  | .atom e => return .atom (← expr e)
  | .proofLeaf t => return .proofLeaf (← expr t)
  | .expanded e p => return .expanded (← expr e) (← child p)
  | .typeNode p => return .typeNode (← child p)
  | .audit input body => return .audit (← child input) (← child body)
  | .app f a => return .app (← child f) (← child a)
  | .lam t b bi => return .lam (← child t) (← bound b) bi
  | .forallE t b bi => return .forallE (← child t) (← bound b) bi
  | .letE t v b nd => return .letE (← child t) (← child v) (← bound b) nd
  | .mdata m b => return .mdata m (← child b)
  | .proj n i b => return .proj n i (← child b)

def substituteExpr (body argument : Expr) (cutoff : Nat := 0) (fuel : Nat := 524288) :=
  run (raw (.substitute argument) body cutoff 0) fuel

def liftExpr (e : Expr) (cutoff amount : Nat) (fuel : Nat := 524288) :=
  run (raw (.lift amount) e cutoff 0) fuel

def abstractExpr (e : Expr) (id : FVarId) (cutoff : Nat := 0) (fuel : Nat := 524288) :=
  run (raw (.abstract id) e cutoff 0) fuel

def instantiateExpr (e : Expr) (parameters : List Name) (values : List Level)
    (fuel : Nat := 524288) :=
  run (raw (.universes parameters values) e 0 0) fuel

def toExpr (p : PlanNode) (fuel : Nat := 524288) := run (materialize p 0) fuel

def abstractPlan (p : PlanNode) (id : FVarId) (fuel : Nat := 524288) :=
  run (transform (.abstract id) none p 0 0) fuel

def instantiatePlan (p : PlanNode) (parameters : List Name) (values : List Level)
    (fuel : Nat := 524288) :=
  run (transform (.universes parameters values) none p 0 0) fuel

def substitutePlan (body argument : PlanNode) (fuel : Nat := 524288) :=
  run (do
    -- Materialize once, retaining the original plan for origin-preserving
    -- replacement. Raw expansion/proof syntax uses the same charged value.
    let expression ← materialize argument 0
    transform (.substitute expression) (some argument) body 0 0) fuel

end PlanTransform

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
  compatibilityVersion : Nat := 7
  compiler : String
  toolchain : String
  policyIdentity : String
  sourceInputs : Array SourceInput
  name : Name
  definitionOwner : Name
  enrollmentOwner : Name
  levelParams : List Name
  slots : Array Slot
  constructorTypes : Array Name := #[]
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

/- Bounded decoder for the canonical token-interned plan payload. The
persistent extension stores bytes, so none of these nodes exist before its
framing and aggregate-budget checks. Allocation debit is conservative and
includes token copies, collection slots and expression/plan constructors. -/
namespace PlanDecoder

private structure State where
  bytes : ByteArray
  offset : Nat := 0
  allocationRemaining : Nat
  levelParams : List Name := []
  tokens : Array String := #[]
  tokenSet : Std.HashSet String := {}
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

private def token (shared : Bool := true) : M String := do
  let state ← get
  let mut cursor := state.offset
  let reference := cursor < state.bytes.size && state.bytes[cursor]! == 64
  if reference then
    unless shared do fail
    cursor := cursor + 1
  let mut length := 0
  let mut digits := 0
  while cursor < state.bytes.size && state.bytes[cursor]! != 58 do
    let c := state.bytes[cursor]!.toNat
    unless 48 ≤ c && c ≤ 57 && digits < 5 do fail
    if digits == 1 && length == 0 then fail
    length := 10 * length + c - 48
    cursor := cursor + 1
    digits := digits + 1
  unless digits > 0 && cursor < state.bytes.size do fail
  if reference then
    let some value := state.tokens[length]? | fail
    -- References reuse a retained String; no new copy or table entry exists.
    modify fun s => { s with offset := cursor + 1 }
    return value
  unless length ≤ state.bytes.size - (cursor + 1) do fail
  -- Literal copies and both interning collection entries are debited before
  -- allocation. Shared strings do not multiply this cost on later references.
  allocate (3 * length + if shared then 192 else 64)
  let some value := String.fromUTF8? (state.bytes.extract (cursor + 1) (cursor + 1 + length)) | fail
  if shared then
    if state.tokenSet.contains value then fail
    modify fun s => { s with tokens := s.tokens.push value, tokenSet := s.tokenSet.insert value }
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
  | "proof-leaf" => return .proofLeaf (← raw)
  | "type-node" => return .typeNode (← child)
  | "audit-input" => return .audit (← child) (← child)
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
  expect "DTR-checked-plan-v5"
  for version in #[1, 1, 1, 7] do unless (← natural) == version do fail
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
  let constructorTypes ← sequence 4096 name
  let sourceInputs ← sequence 4096 do
    let path ← token
    let sha256 ← digest
    return { path, sha256 : SourceInput }
  let rules ← sequence 4096 token
  let work ← token false
  let some chargedWork := work.toNat? | fail
  unless work.utf8ByteSize == 6 && work.all Char.isDigit && chargedWork ≤ 524288 do fail
  let typePlan ← plan
  let bodyPlan ← plan
  return {
    compiler, toolchain, policyIdentity, sourceInputs, name := templateName,
    definitionOwner, enrollmentOwner, levelParams, slots, typeIdentity, bodyIdentity,
    dependencies, constructorTypes, plan := bodyPlan, typePlan, rules, chargedWork, planIdentity := "", serializedBytes := 0 }

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

structure TemplateBindingClaim where
  key : TemplateOccurrenceKey
  arena : Expr
  descriptor : Option Expr
  resolutionDiagnostic : Option String := none
  escapeInput : EscapeRecordInput := {}
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

/-- Exact output of a fixed theorem-producing transaction. This data type and
its matcher grant no write access to the producers' private registries. -/
structure ProducedTheorem where
  owner : Name
  theoremValue : TheoremVal
  deriving Inhabited

def ProducedTheorem.matches (record : ProducedTheorem) (env : Environment) : Bool :=
  let expected := record.theoremValue
  let owner := match env.getModuleIdxFor? expected.name with
    | some index => env.header.moduleNames[index.toNat]!
    | none => env.header.mainModule
  owner == record.owner && match env.find? expected.name with
    | some (.thmInfo actual) => actual.levelParams == expected.levelParams &&
        actual.type == expected.type && actual.value == expected.value
    | _ => false

/-- Read-only fixed-producer API, resolved by exact declaration and module owner. -/
abbrev GeneratedCompanionReportDriver := Environment → Array Name

end LeanInformationAudit

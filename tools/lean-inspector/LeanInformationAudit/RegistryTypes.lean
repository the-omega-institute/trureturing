import LeanInformationAuditInterface.Store

/- Implementation-owned plans and record computations.
Stable declaration records are defined in the Interface package. -/
namespace LeanInformationAudit

open Lean

namespace TemplateAudit

register_option informationTemplate.work : Nat := {
  defValue := 524288
  descr := "Lower-only DTR expression, substitution and byte-work quota" }


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
  compatibilityVersion : Nat := 10
  compiler : String
  toolchain : String
  name : Name
  definitionOwner : Name
  enrollmentOwner : Name
  levelParams : List Name
  slots : Array Slot
  sourceBound : Bool := false
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

end TemplateAudit

def CatalogKind.artifactName : CatalogKind -> String
  | .canonicalMaximal => "canonical_maximal"
  | .analysisView => "analysis_view"

def InformationRegistryEntry.canonicalObjectArenaName
    (entry : InformationRegistryEntry) : Name :=
  if !entry.resolvedArenaName.isAnonymous then entry.resolvedArenaName
  else if entry.objectArenaName.isAnonymous then entry.arenaName else entry.objectArenaName

def InformationRegistryEntry.effectiveCatalogId
    (entry : InformationRegistryEntry) : CatalogId :=
  if entry.catalogId.isAnonymous then entry.canonicalObjectArenaName else entry.catalogId

def OccurrenceCertificate.name : OccurrenceCertificate → Name
  | .positive name | .trivial name => name

def OccurrenceCertificate.suffix : OccurrenceCertificate → String
  | .positive _ => "__lowers_escape"
  | .trivial _ => "__trivial_in_catalog"

def CatalogVerdict.name : CatalogVerdict → Name
  | .irredundant name | .redundant name => name

def CatalogVerdict.label : CatalogVerdict → String
  | .irredundant _ => "irredundant"
  | .redundant _ => "redundant"

def CatalogVerdict.suffix : CatalogVerdict → String
  | .irredundant _ => "__catalog_irredundant"
  | .redundant _ => "__catalog_redundant"

def SealTheoremRecord.certificateName (row : SealTheoremRecord) : Name := row.certificate.name

end LeanInformationAudit

namespace LeanInformationAudit
open Lean

/-- Judge-owned semantic API for the lightweight standalone report driver.
The inspector resolves one exact declaration/owner of this type. Content does
not register producers, callbacks, policies or acceptance bits. Each requested
target yields, from its own assessment: its binding row, the generated
declarations it owns, and the environment in which they were generated. The
type uses core types only because the inspector does not import the judge. -/
abbrev InformationTemplateReportDriver := Array Name → MetaM (Array (Json × Array Name × Environment))

/-- Original registration root, immutable environment input and caller-selected
options. Both command and report consumers pass the same explicit inputs. -/
structure RegistrationAssessmentInput where
  rootId : Name
  environment : Environment
  options : Options

def RegistrationAssessmentInput.capture {m : Type → Type} [Monad m] [MonadEnv m]
    [MonadOptions m] (rootId : Name) : m RegistrationAssessmentInput := do
  return { rootId, environment := ← getEnv, options := ← getOptions }

private def environmentConstantNames (constants : ConstMap) : Array Name :=
  (SMap.toList constants).toArray.map (·.1) |>.qsort Name.quickLt

/-- Command lifts can rebuild the wrapper while preserving kernel inputs.
Adding a declaration invalidates a captured assessment input. -/
def sameRegistrationEnvironment (a b : Environment) : Bool :=
  a.header.mainModule == b.header.mainModule &&
    a.allImportedModuleNames == b.allImportedModuleNames &&
    -- Command lifts can share the immutable constant map across wrappers.
    -- The proof required by withPtrEq keeps the original comparison as its
    -- logical definition and as the runtime fallback for different maps.
    withPtrEq (Environment.constants a) (Environment.constants b)
      (fun _ => environmentConstantNames (Environment.constants a) ==
        environmentConstantNames (Environment.constants b))
      (by intro h; simp only [h, beq_self_eq_true])

end LeanInformationAudit


namespace LeanInformationAudit.TemplateAudit
open Lean

/-- A byte-radix tree. Each node has at most 256 sorted outgoing byte edges;
lookup visits only the selected key's path, never the collection of templates. -/
inductive TemplateTrie where
  | node (value : Option TemplatePlanData) (edges : Array (UInt8 × TemplateTrie))
  deriving Inhabited

namespace TemplateTrie
partial def insertAt (tree : TemplateTrie) (key : ByteArray) (offset : Nat)
    (value : TemplatePlanData) : TemplateTrie := Id.run do
  let .node old edges := tree
  if offset == key.size then return .node (some value) edges
  let byte := key[offset]!
  let mut found := false
  let mut next := edges.map fun (b, child) =>
    if b == byte then
      (b, insertAt child key (offset + 1) value)
    else (b, child)
  for (b, _) in edges do if b == byte then found := true
  if !found then
    next := next.push (byte, insertAt (.node none #[]) key (offset + 1) value)
  return .node old (next.qsort fun a b => a.1 < b.1)

/-- The callback observes actual node/edge visits. It cannot change the lookup. -/
partial def lookupAt [Monad m] (tree : TemplateTrie) (key : ByteArray)
    (offset : Nat) (observe : m Unit) : m (Option TemplatePlanData) := do
  observe
  let .node value edges := tree
  if offset == key.size then return value
  let byte := key[offset]!
  for (b, child) in edges do
    observe
    if b == byte then return ← lookupAt child key (offset + 1) observe
    if b > byte then return none
  return none

end TemplateTrie

end LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.TemplateBinding
open Lean

private structure AssessmentRecords where
  events : Array (Name × TemplateOccurrenceEvent) := #[]
  claims : Array (Name × TemplateBindingClaim) := #[]
  records : Array (Name × BindingRecord) := #[]
  deriving Inhabited

private initialize assessmentRecords : EnvExtension AssessmentRecords ←
  registerEnvExtension (pure {})

def resetAssessmentRecords (env : Environment) : Environment := assessmentRecords.setState env {}

def addOccurrence (env : Environment) (event : TemplateOccurrenceEvent) :
    Environment :=
  assessmentRecords.modifyState env fun state => { state with
    events := state.events.push (event.key.registrationModule, event) }

def addClaim (env : Environment) (claim : TemplateBindingClaim) : Environment :=
  assessmentRecords.modifyState env fun state => { state with
    claims := state.claims.push (claim.owner, claim) }

def addRecord (env : Environment) (record : BindingRecord) : Environment :=
  assessmentRecords.modifyState env fun state => { state with
    records := state.records.push (record.occurrence.key.registrationModule, record) }

def ownedEvents (env : Environment) : Array (Name × TemplateOccurrenceEvent) :=
  (assessmentRecords.getState env).events
def ownedClaims (env : Environment) : Array (Name × TemplateBindingClaim) :=
  (assessmentRecords.getState env).claims
def ownedRecords (env : Environment) : Array (Name × BindingRecord) :=
  (assessmentRecords.getState env).records
def inventory (env : Environment) : Array TemplateOccurrenceEvent := (ownedEvents env).map Prod.snd
def claims (env : Environment) : Array TemplateBindingClaim := (ownedClaims env).map Prod.snd
def records (env : Environment) : Array BindingRecord := (ownedRecords env).map Prod.snd

end LeanInformationAudit.TemplateBinding

namespace LeanInformationAudit.GeneratedDeclarations
open Lean
private structure State where
  owner : Option Name := none
  names : Array (Name × Name) := #[]
  deriving Inhabited
private initialize state : EnvExtension State ← registerEnvExtension (pure {})

def entries (env : Environment) : Array (Name × Name) := (state.getState env).names

def currentOwner (env : Environment) : Name :=
  (state.getState env).owner.getD env.header.mainModule

def ownerOf (env : Environment) (name : Name) : Name :=
  ((entries env).find? (·.1 == name)).map Prod.snd |>.getD
    ((env.getModuleIdxFor? name).map (env.header.moduleNames[·.toNat]!) |>.getD env.header.mainModule)

def record (env : Environment) (name : Name) : Environment :=
  let current := state.getState env
  let owner := current.owner.getD env.header.mainModule
  if (entries env).any (·.1 == name) then env else
    state.setState env { current with names := current.names.push (name, owner) }

def withOwner {m : Type → Type} [Monad m] [MonadEnv m] [MonadFinally m]
    (owner : Name) (action : m α) : m α := do
  let previous := (state.getState (← getEnv)).owner
  modifyEnv fun env => state.modifyState env fun current => { current with owner := some owner }
  try action finally
    modifyEnv fun env => state.modifyState env fun current => { current with owner := previous }
end LeanInformationAudit.GeneratedDeclarations

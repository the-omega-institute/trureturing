import LeanInformationAudit.TemplateEnrollment
import LeanInformationAudit.Registry.Repository

namespace LeanInformationAudit.CompiledEvidence
open Lean TemplateAudit

abbrev Q := RegistrationGates.QueryM
private def fail [Monad m] [MonadLiftT IO m] (reason : String) : m α :=
  liftM (m := IO) (throw (IO.userError reason) : IO α)

private def objectDomainArenaName :=
  `D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena

private def getConstInfo (name : Name) : Q ConstantInfo := do
  let some info := (← read).view.find? name
    | fail s!"incomplete_closure:dtr.compiled_constant:{name}"
  return info
private def projectType (e : Expr) : Q Expr :=
  RegistrationGates.compiledQuery (Contract.CompiledExpressions.typeShape e)
private def sameShape (a b : Expr) : Q Bool :=
  RegistrationGates.compiledQuery (Contract.CompiledExpressions.sameShape a b)
private def isProp (e : Expr) : Q Bool :=
  RegistrationGates.compiledQuery (Contract.CompiledExpressions.propositionShape e)
private def isProof (e : Expr) : Q Bool := do isProp (← projectType e)
private def isType (e : Expr) : Q Bool := do
  RegistrationGates.compiledQuery (do
    return (← Contract.CompiledExpressions.head (← Contract.CompiledExpressions.typeShape e)).isSort)

private def withLocal (name : Name) (bi : BinderInfo) (type : Expr)
    (value : Option Expr) (body : Expr → Q α) : Q α := do
  let context ← read
  let mut index := context.locals.numIndices
  while context.locals.contains ⟨Name.num `compiledEvidenceLocal index⟩ do index := index + 1
  let id : FVarId := ⟨Name.num `compiledEvidenceLocal index⟩
  let locals := match value with
    | none => context.locals.mkLocalDecl id name type bi
    | some value => context.locals.mkLetDecl id name type value
  withReader (fun context : RegistrationGates.QueryContext => { context with locals })
    (body (mkFVar id))

/-- Named record members use their compiled projection layout or their
receiver's rigid universe telescope. No implicit argument is synthesized. -/
private def recordApplication (name : Name) (base : Expr) : Q Expr := do
  if let some projection := (← read).view.getProjectionFnInfo? name then
    let .ctorInfo ctor ← getConstInfo projection.ctorName
      | fail s!"incomplete_closure:dtr.compiled_projection:{name}"
    return .proj ctor.induct projection.i base
  let type ← RegistrationGates.compiledQuery <|
    Contract.CompiledExpressions.head (← projectType base)
  let .const _ levels := type.getAppFn
    | fail s!"incomplete_closure:dtr.record_type:{name}"
  let info ← getConstInfo name
  unless levels.length == info.levelParams.length do
    fail s!"incomplete_closure:dtr.record_universes:{name}"
  return mkApp (mkConst name levels) base

private structure NormalizedArena where
  original : Expr
  law : Expr
  finite : Expr
  domain : Option Expr

private def normalizeArena (arena : Expr) : Q NormalizedArena := do
  let type ← RegistrationGates.compiledQuery <|
    Contract.CompiledExpressions.head (← projectType arena)
  let objectDomain := type.isConstOf objectDomainArenaName
  let law ← if objectDomain then recordApplication (objectDomainArenaName.str "toPrimitiveLawArena") arena
    else pure arena
  let finite ← if objectDomain ||
      type.isConstOf `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena then
      recordApplication `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena law
    else if type.isConstOf `D5.S3.ConceptDynamics.InformationEscape.Arena then pure arena
    else fail "IE-C003 ArenaResolutionFailed"
  let domain ← if objectDomain then
      some <$> recordApplication (objectDomainArenaName.str "Domain") arena
    else pure none
  return { original := arena, law, finite, domain }

/-- Proof-opaque syntax comes from compiled declaration types and the current
lexical binder table. The calculator has no Environment or Meta operations. -/
def eraseProofs (e : Expr) (fuel : Nat := 524288) : Q (Expr × Nat) := do
  RegistrationGates.compiledQueryWork (Contract.CompiledExpressions.erase e) fuel

/-- Proof-opaque source data fingerprint, sharing repeated raw type subtrees. -/
def compactIdentity (params : List Name) (e : Expr) (fuel : Nat := 524288) :
    Q (Except String (String × Nat)) := do
  let (erased, work) ← eraseProofs e fuel
  return (compactRawIdentity params erased (fuel - work)).map fun (identity, cost) =>
    (identity, cost + work)

/-- The forward bridge is recognized by its type name, without importing content
into the finite seal closure. Both bridges retain the exact statement check. -/
def escapeForwardBridge : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization

def bridgeKind (event : TemplateOccurrenceEvent) : Q String := do
  let type := (← getConstInfo event.realizationName).type
  return if type.isAppOfArity
      `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration 2 then "source-equivalence"
    else if type.isAppOfArity escapeForwardBridge 3 then "forward" else "legacy"

/-- Only closed, zero-parameter Prop definitions occurring in the original
statement qualify. A definition discovered in one of their bodies is not visited. -/
def statementDefinitions (statement : Expr) : Q (Array Name) := do
  let originalNames := statement.getUsedConstants
  let (statement, _) ← eraseProofs statement
  let mut names := #[]
  for name in statement.getUsedConstants do
    unless originalNames.contains name do continue
    if let .defnInfo info ← getConstInfo name then
      if info.levelParams.isEmpty && (← sameShape info.type (mkSort .zero)) &&
          !info.value.hasFVar && !info.value.hasMVar && !info.value.hasLooseBVars then
        names := names.push name
  return names

private partial def bodyContainsOrigin (body origin : Expr) (depth : Nat := 0) : Q Bool := do
  if depth > 256 then fail "incomplete_closure:dtr.statement_depth"
  if ← isProof body then return false
  if body.equal origin then return true
  let child := fun e => bodyContainsOrigin e origin (depth + 1)
  match body with
  | .app f a => return (← child f) || (← child a)
  | .lam name type body bi | .forallE name type body bi =>
    if ← child type then return true
    withLocal name bi type none fun x => child (body.instantiate1 x)
  | .letE name type value body _ =>
    if (← child type) || (← child value) then return true
    withLocal name .default type (some value) fun x => child (body.instantiate1 x)
  | .mdata _ body | .proj _ _ body => child body
  | _ => return false

def statementContainsOrigin (statement origin : Expr) : Q Bool := do
  if (statement.find? (·.equal origin)).isSome then return true
  for name in ← statementDefinitions statement do
    let .defnInfo info ← getConstInfo name | continue
    if ← bodyContainsOrigin info.value origin then return true
  return false

/-- Semantic inputs used outside template extraction must also bind evidence
and its cache. These are names only; the content module is never imported here. -/
def inspectionRoots (event : TemplateOccurrenceEvent) : Q (Array Name) := do
  let roots ← statementDefinitions event.statement
  return roots

/-- Retain the inspected definitions and their repository data/type closure,
including Interface records and Reg support at their compiler source owners.
Proof leaves contribute their types only; imported compiler data supplies
the upstream declaration identities. -/
def inspectionDependencies (event : TemplateOccurrenceEvent) : Q (Array Name) := do
  let mut pending := (← inspectionRoots event).toList
  let mut seen : NameSet := {}
  let mut remaining := 524288
  while let name :: rest := pending do
    pending := rest
    if name == ``lcProof || seen.contains name then continue
    if remaining == 0 then fail "incomplete_closure:dtr.inspection_inputs"
    remaining := remaining - 1
    seen := seen.insert name
    let info ← getConstInfo name
    let some owner := (← read).view.ownerOf name
      | fail s!"incomplete_closure:dtr.inspection_owner:{name}"
    let (type, work) ← eraseProofs info.type remaining
    remaining := remaining - work
    pending := type.getUsedConstants.toList ++ pending
    if Repository.isModule owner && !(← isProp info.type) then
      if let some value := info.value? then
        let (value, work) ← eraseProofs value remaining
        remaining := remaining - work
        pending := value.getUsedConstants.toList ++ pending
  return seen.toArray

private def escapeIdentity (params : List Name) (value : Expr) : Q String := do
  let .ok (identity, _) := rawStatementIdentity params value
    | fail "incomplete_closure:dtr.escape_identity"
  return identity

/-- This check consumes only names, expression occurrences and compiled types.
No state, chain, certificate body, or residual count is evaluated. -/
def checkEscapeRecord (event : TemplateOccurrenceEvent) (input : EscapeRecordInput) :
    Q EscapeRecordEvidence := do
  let kind ← bridgeKind event
  if kind == "source-equivalence" then
    let continuation : Option EscapeContinuationIdentity :=
      if input.openContinuation then some { kind := "open" } else none
    return { bridgeKind := kind, continuation }
  -- Structural registrations without escape slots do not consume a finite arena.
  if input.fromObject.isNone && input.continuation.isNone then
    let continuation := if input.openContinuation then
      some ({ kind := "open" } : EscapeContinuationIdentity) else none
    return { bridgeKind := kind, continuation }
  let normalized ← normalizeArena event.arena
  let arena := normalized.finite
  let fromObject ← input.fromObject.mapM fun origin => do
    unless ← statementContainsOrigin event.statement origin do
      fail "unclassified_form:dtr.escape_from_absent"
    let some name := origin.getAppFn.constName?
      | fail "unclassified_form:dtr.escape_from_identity"
    if origin.hasFVar || origin.hasMVar || origin.hasLooseBVars then
      fail "unclassified_form:dtr.escape_from_identity"
    let type ← projectType origin
    let state ← match normalized.domain with
        | some domain => pure domain
        | none => recordApplication `D5.S3.ConceptDynamics.InformationEscape.Arena.State arena
    let represented := if ← isType origin then origin else type
    unless ← sameShape represented state do
      fail "unclassified_form:dtr.escape_from_state"
    let typeIdentity ← escapeIdentity event.levelParams type
    let objectIdentity ← escapeIdentity event.levelParams origin
    return (⟨name, typeIdentity, objectIdentity⟩ : EscapeFromIdentity)
  let continuation ← if input.openContinuation then
      if input.continuation.isSome then fail "unclassified_form:dtr.escape_continues_kind"
      pure <| some { kind := "open" : EscapeContinuationIdentity }
    else input.continuation.mapM fun value => do
      let .const declarationName levels := value
        | fail "unclassified_form:dtr.escape_continues_named_certificate"
      let info ← getConstInfo declarationName
      unless levels.length == info.levelParams.length do
        fail "unclassified_form:dtr.escape_continues_named_certificate"
      let type ← projectType value
      let kind ← if type.isAppOfArity
          `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapeResidualWitness 2 then
          pure "witness"
        else if type.isAppOfArity
          `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapeResidualEmpty 2 then
          pure "empty"
        else fail "unclassified_form:dtr.escape_continues_kind"
      let args := type.getAppArgs
      let chain := args[1]!
      let .const chainName _ := chain
        | fail "unclassified_form:dtr.escape_continues_named_chain"
      let chainType ← projectType chain
      unless chainType.isAppOfArity `D5.S3.ConceptDynamics.InformationEscape.LayerChain 1 &&
          (← sameShape args[0]! arena) && (← sameShape chainType.appArg! arena) do
        fail "unclassified_form:dtr.escape_continues_arena"
      if kind == "witness" then
        let membership ← recordApplication
          `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapeResidualWitness.unresolved value
        unless ← isProof membership do fail "unclassified_form:dtr.escape_continues_membership"
        unless (← projectType membership).isAppOf ``Membership.mem do
          fail "unclassified_form:dtr.escape_continues_membership"
      else unless ← isProof value do fail "unclassified_form:dtr.escape_continues_kind"
      let statementIdentity ← escapeIdentity info.levelParams info.type
      return (⟨kind, some declarationName, some statementIdentity, some chainName⟩ :
        EscapeContinuationIdentity)
  return { fromObject, continuation, bridgeKind := (← bridgeKind event) }

/-- Typed identity stops at each proof and serializes its proposition instead.
The pure wire encoder is exposed separately for synthetic encoding tests. -/
def rawIdentity (params : List Name) (e : Expr) (fuel : Nat := 524288) :
    Q (Except String (String × Nat)) := do
  let (erased, work) ← eraseProofs e fuel
  return (compactRawIdentity params erased (fuel - work)).map fun (identity, bytes) =>
    (identity, work + bytes)

end LeanInformationAudit.CompiledEvidence

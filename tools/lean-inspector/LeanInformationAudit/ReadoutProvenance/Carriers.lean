import LeanInformationAudit.ReadoutProvenance.State
namespace LeanInformationAudit.RegistrationGates
open Lean

/-- Reuse statement syntax only within one binding-validation scope. -/
def withCompiledAliasMemo (action : QueryM α) : QueryM α := do
  let session ← querySession
  let previous := (← session.get).aliasMemo
  session.modify fun state => { state with aliasMemo := (true, none) }
  try action
  finally session.modify fun state => { state with aliasMemo := previous }

-- Pointer equality is only a sufficient cache-hit key. A miss runs the original
-- bounded normalizer; unlike hash equality, it cannot confuse distinct syntax.
private def sameStatementObject {α : Type} (a b : α) : Bool := unsafe ptrEq a b



def aliasBody (value : Expr) (args : Array Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal (args.size + 1) do return none
  let application := mkAppN value args
  let (result, work) ← boundQueryWork (exactNodeHead application) (← get).exprFuel
  unless ← chargeTraversal work do return none
  if result.equal application && !args.isEmpty && application.getAppFn.isLambda then return none
  return some result

partial def representationType (type : Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  match type with
  | .mdata _ body => representationType body
  | .fvar id =>
    let some value := (← localDeclaration id).value? (allowNondep := true) | return some type
    representationType value
  | _ => return some type

-- A field role needs a positive spelling: kind alone cannot distinguish a
-- carrier slot from an ordinary value. Explicit aliases are followed before
-- deciding the role; no recursor or opaque carrier is evaluated. These witnesses
-- discharge only the role check. observedType still checks all parameters,
-- proof identities and nominal fields of the recognized value type.
partial def nominalFieldShape (env : CompiledView) (type : Expr)
    (parameters : Array Expr) : WalkM (Option ProvenanceAdmissionWitness) := do
  let some concrete ← representationType type | return none
  let some kind ← occurrenceType concrete | return none
  if kind == .sort .zero then
    -- admission-exit: nominalFieldShape.1 rule=fieldProposition
    return some (witness .fieldProposition concrete)
  match concrete with
  | .sort _ => return none
  | .forallE n domain body bi =>
    let result ← withCompiledLocal n bi domain fun x => do
      let some body ← substitute body #[x] | return none
      -- admission-exit: nominalFieldShape.forward.1 rule=retained-witness.rule
      nominalFieldShape env body parameters
    if result.isNone then return none
    -- admission-exit: nominalFieldShape.2 rule=fieldFunction
    return some (witness .fieldFunction concrete)
  | .letE _ _ value body _ =>
    let some body ← substitute body #[value] | return none
    let some _ ← nominalFieldShape env body parameters | return none
    -- admission-exit: nominalFieldShape.3 rule=fieldAlias
    return some (witness .fieldAlias concrete)
  | _ =>
    let some (head, args) ← applicationParts concrete | return none
    unless ← chargeTraversal parameters.size do return none
    -- Supplied parameters can be projections or instantiated types, not only
    -- local variable heads. This witnesses their role; observedType still
    -- checks the entire instantiated parameter for statement-bearing inputs.
    if parameters.contains concrete || (head.isFVar && parameters.contains head) then
      -- admission-exit: nominalFieldShape.4 rule=fieldParameter
      return some (witness .fieldParameter concrete)
    if let .lam .. := head then
      let some body ← aliasBody head args | return none
      let some _ ← nominalFieldShape env body parameters | return none
      -- admission-exit: nominalFieldShape.5 rule=fieldAlias
      return some (witness .fieldAlias concrete)
    let .const name levels := head | return none
    let some declaration := env.find? name | return none
    match declaration with
    | .inductInfo _ | .quotInfo _ =>
      -- admission-exit: nominalFieldShape.6 rule=fieldConcrete
      return some (witness .fieldConcrete concrete)
    | .defnInfo _ =>
      let (body, work) ← boundQueryWork (exactNodeHead concrete) (← get).exprFuel
      unless ← chargeTraversal work do return none
      if body == concrete then return none
      let some _ ← nominalFieldShape env body parameters | return none
      -- admission-exit: nominalFieldShape.7 rule=fieldAlias
      return some (witness .fieldAlias concrete)
    | _ => return none

-- Decode only an explicit record projection. The receiver must expose a
-- constructor of the projection's own structure; computed recursors stay opaque.
private inductive StatementStep where
  | next (expression : Expr)
  | recognized (evidence : ProvenanceAdmissionWitness)
  | unclassified (site : Unclassified)
  | incomplete

private def statementUnknown (head : Expr) : WalkM StatementStep := do
  let name := head.constName?.getD (match head with
    | .proj structureName _ _ => structureName
    | .fvar _ => `fvar
    | .bvar _ => `bvar
    | .lam .. => `lambda
    | _ => `unrecognized_head)
  return .unclassified ⟨"unclassified_statement_head", name,
    namespaceLabel (← getCompiledView) name, (← get).theoremName⟩

def statementStep (env : CompiledView) (current : Expr) : WalkM StatementStep := do
  let some (head, _) ← applicationParts current | return .incomplete
  if current.isForall then return .recognized (witness .statementForall current)
  if let .const name _ := head then
    if (env.find? name).any (fun info => match info with
        | .inductInfo _ => true | _ => false) then
      return .recognized (witness .statementInductive current)
  let (next, work) ← boundQueryWork (exactNodeHead current) (← get).exprFuel
  unless ← chargeTraversal work do return .incomplete
  if next.equal current then statementUnknown head else return .next next

private partial def statementOuter (env : CompiledView) (type : Expr) :
    WalkM (Option ProvenanceAdmissionWitness) := do
  unless ← chargeTraversal do return none
  if type.getAppFn.isConstOf `Multiset.Mem then
    -- admission-exit: statementOuter.1 rule=statementMembership
    return some (witness .statementMembership type)
  match ← statementStep env type with
  -- admission-exit: statementOuter.2 rule=retained-witness.rule
  | .recognized evidence => return some evidence
  | .unclassified _ => return none
  | .incomplete => noteIncomplete `incomplete_classification `type_classification; return none
  | .next next =>
    if next == type then return none
    -- admission-exit: statementOuter.forward.1 rule=retained-witness.rule
    statementOuter env next

-- Equality-only List metadata has recursive List premises and disequalities
-- ending in False. These explicit positive conclusions, or negations of known
-- non-equality heads, cannot be those premises. Unknown predicate heads stop.
partial def listStatementBoundary (env : CompiledView) (type : Expr)
    (binders : Nat := 0) : WalkM (Option ProvenanceAdmissionWitness) := do
  let some evidence ← statementOuter env type | return none
  let type := evidence.matchedType
  match type with
  | .forallE n domain body bi =>
    if binders == 0 then
      let some firstProof ← boundedQuery (typedNodeProp domain) `list_statement_domain | return none
      if !firstProof then
        let twoDataBinders ← withCompiledLocal n bi domain fun x => do
          let some body ← substitute body #[x] | return false
          let some evidence ← statementOuter env body | return false
          let body := evidence.matchedType
          let .forallE _ secondDomain _ _ := body | return false
          let some secondProof ← boundedQuery (typedNodeProp secondDomain) `list_statement_domain
            | return false
          return !secondProof
        -- admission-exit: listStatementBoundary.1 rule=listForall
        if twoDataBinders then return some (witness .listForall type)
    if body.isConstOf ``False then
      let some evidence ← statementOuter env domain | return none
      let domain := evidence.matchedType
      if domain.isForall || domain.getAppFn.constName?.any
          (#[``Exists, ``And, ``Or, ``List.Mem, `Multiset.Mem].contains ·) then
        -- admission-exit: listStatementBoundary.2 rule=listNegated
        return some (witness .listNegated type)
      return none
    withCompiledLocal n bi domain fun x => do
      let some body ← substitute body #[x] | return none
      -- admission-exit: listStatementBoundary.forward.1 rule=retained-witness.rule
      listStatementBoundary env body (binders + 1)
  | _ =>
    let name := type.getAppFn.constName?.getD .anonymous
    if #[``And, ``Or, ``Exists, ``True, ``Eq, ``HEq, ``Nat.le].contains name ||
        (binders > 0 && #[``List.Mem, `Multiset.Mem].contains name) then
      -- admission-exit: listStatementBoundary.3 rule=listPositive
      return some (witness .listPositive type)
    return none

-- Pure data carriers for equality-only collection metadata. The surrounding
-- type fold has already checked actual parameters and statement-bearing fields.
-- Nominal carriers with proof/type-valued fields are excluded here; intrinsic
-- scalar bounds and quotient containers have explicit representation boundaries.
partial def dataCarrier (env : CompiledView) (type : Expr)
    (active : Array Expr := #[]) : WalkM (Option ProvenanceAdmissionWitness) := do
  unless ← chargeTraversal do return none
  let some type ← representationType type | return none
  let some kind ← occurrenceType type | return none
  let .sort level := kind | return none
  unless level.isNeverZero do return none
  match type with
  | .sort _ => return none
  | .fvar id =>
    if (← localDeclaration id).value? (allowNondep := true) |>.isNone then
      -- admission-exit: dataCarrier.1 rule=rigidCarrier
      return some (witness .rigidCarrier type)
    return none
  | .proj structureName index receiver =>
    -- Only registered arena/signature carrier selectors inherit the rigid
    -- local parameter boundary. Concrete receivers expose their actual field,
    -- which must pass the same carrier test (including Prop/payload fences).
    let audited := carrierHeads.any fun selector =>
      match env.getProjectionFnInfo? selector with
      | some projection => projection.i == index &&
        (env.find? projection.ctorName).any fun info =>
          match info with
          | .ctorInfo info => info.induct == structureName
          | _ => false
      | none => false
    unless audited do return none
    let some receiver ← representationType receiver | return none
    if let .fvar id := receiver then
      if (← localDeclaration id).value? (allowNondep := true) |>.isNone then
        -- admission-exit: dataCarrier.2 rule=carrierProjection
        return some (witness .carrierProjection type)
    let .next field ← statementStep env (.proj structureName index receiver) | return none
    if field == type then return none
    -- admission-exit: dataCarrier.forward.1 rule=retained-witness.rule
    dataCarrier env field active
  | .forallE n domain body bi =>
    unless (← dataCarrier env domain active).isSome do return none
    withCompiledLocal n bi domain fun x => do
      let some body ← substitute body #[x] | return none
      -- admission-exit: dataCarrier.forward.2 rule=retained-witness.rule
      dataCarrier env body active
  | _ =>
    let some (head, args) ← applicationParts type | return none
    let .const name levels := head | return none
    if #[``Nat, ``Int, `Rat, ``Fin, `ZMod].contains name then
      -- admission-exit: dataCarrier.3 rule=scalarCarrier
      return some (witness .scalarCarrier type)
    if #[``List, `Multiset, `Finset].contains name && args.size == 1 then
      -- admission-exit: dataCarrier.4 rule=retained-witness.rule
      return ← dataCarrier env args[0]! active
    if name == ``Subtype && args.size == 2 then
      -- admission-exit: dataCarrier.5 rule=retained-witness.rule
      return ← dataCarrier env args[0]! active
    if active.contains type then return none
    if let some (.defnInfo info) := env.find? name then
      let value ← compiledValue (.defnInfo info) levels
      let some body ← aliasBody value args | return none
      -- admission-exit: dataCarrier.6 rule=retained-witness.rule
      return ← dataCarrier env body (active.push type)
    let some branches ← caseFields type | return none
    for (lctx, fields) in branches do
      for field in fields do
        let clean ← withCompiledLocals lctx do
          let some fieldType ← occurrenceType field | return none
          -- admission-exit: dataCarrier.forward.3 rule=retained-witness.rule
          dataCarrier env fieldType (active.push type)
        unless clean.isSome do return none
    -- admission-exit: dataCarrier.7 rule=nominalCarrier
    return some (witness .nominalCarrier type)

-- Record explicit proposition-alias spellings only as rejection witnesses.
-- These hashes never certify non-mention and never normalize data operands.
private def statementAliasesCore (env : CompiledView) : WalkM Unit := do
  let mut current := (← get).statement
  let mut seen : Std.HashSet UInt64 := {}
  repeat
    unless ← chargeTraversal do return
    if seen.contains (hash current) then
      noteIncomplete `alias_cycle `statement_aliases
      return
    seen := seen.insert (hash current)
    modify fun s => { s with statementForms := s.statementForms.push current }
    match ← statementStep env current with
    | .next body => current := body
    | .recognized evidence =>
      modify fun s => { s with recognizedStatement := some evidence }
      return
    | .unclassified site => noteUnclassified site; return
    | .incomplete => noteIncomplete `incomplete_classification `type_classification; return

/-- Reuse a completed normalization only inside its binding-validation scope.
Every hit pays a lookup debit; all subsequent occurrence checks still run. -/
def statementAliases (env : CompiledView) : WalkM Unit := do
  let state ← get
  let (enabled, cached) := (← (← querySession).get).aliasMemo
  if enabled then
    if let some cached := cached then
      if cached.theoremName == state.theoremName &&
          sameStatementObject cached.statement state.statement &&
          cached.constants.constantsIdentity == env.constantsIdentity &&
          cached.isExporting == env.isExporting then
        unless ← chargeTraversal do return
        modify fun s => { s with
          statementForms := cached.forms
          recognizedStatement := some cached.recognized }
        return
  statementAliasesCore env
  let state ← get
  if enabled && !state.incomplete && state.unclassified.isNone then
    if let some recognized := state.recognizedStatement then
      let cached : StatementAliasMemo :=
        { theoremName := state.theoremName, statement := state.statement,
          constants := env, isExporting := env.isExporting,
          forms := state.statementForms, recognized }
      (← querySession).modify fun state => { state with aliasMemo := (true, some cached) }

-- The final supported outer spelling is used for structural family fences.
-- Computed operands remain untouched and cannot establish non-mention.
def statementBoundary : WalkM (Option ProvenanceAdmissionWitness) := do
  -- admission-exit: statementBoundary.1 rule=retained-witness.rule
  return (← get).recognizedStatement

-- A carrier alias is supported only when its explicit body is another named
-- type application. This recognizes Unit/PUnit without evaluating data or
-- admitting arbitrary computed carriers. The ordinary type fold still checks
-- every parameter and nominal field before this narrower List boundary is used.
partial def namedCarrier (env : CompiledView) (type : Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  let some type ← representationType type | return none
  let .const name levels := type.getAppFn | return some type
  let some (.defnInfo info) := env.find? name | return some type
  let (body, work) ← boundQueryWork (exactNodeHead type) (← get).exprFuel
  unless ← chargeTraversal work do return none
  unless body.getAppFn.isConst do return some type
  if body == type then return none
  namedCarrier env body

private partial def buildBinderContext (context : Array Expr) (k : Array Expr → WalkM α)
    (index : Nat := 0) (locals : Array Expr := #[]) : WalkM (Option α) := do
  unless ← chargeTraversal do return none
  if h : index < context.size then
    -- Parent contexts retain their local arrays while the body runs, so pushing
    -- the next local can copy the prefix as well as append one entry.
    unless ← chargeTraversal (locals.size + 1) do return none
    let next := fun locals => buildBinderContext context k (index + 1) locals
    match context[index] with
    | .lam n t _ bi | .forallE n t _ bi =>
      let some t ← substitute t locals | return none
      withCompiledLocal n bi t fun x => next (locals.push x)
    | .letE n t v _ nd =>
      let some t ← substitute t locals | return none
      let some v ← substitute v locals | return none
      withCompiledLet n t v (fun _ => next (locals.push v)) (nondep := nd)
    | _ =>
      noteUnclassified ⟨"unclassified_binder_context", `binder, "unclassified", `binder⟩
      return none
  else return some (← k locals)

-- Reuse reconstructed binders only when the original parent context is empty.
-- Restoring the lexical binder table preserves actual types and
-- stable fvar identities; nested callers retain their existing parent context.
partial def inBinderContext (context : Array Expr) (k : Array Expr → WalkM α) :
    WalkM (Option α) := do
  if context.isEmpty then return some (← k #[])
  if !(← getQueryLocals).isEmpty then return ← buildBinderContext context k
  unless ← chargeTraversal (2 * context.size + 1) do return none
  if let some (lctx, locals) := (← get).binderContexts[context]? then
    return some (← withCompiledLocals lctx (k locals))
  unless ← chargeTraversal context.size do return none
  -- Canonicalize the parent first: extending a lexical prefix must retain
  -- its immutable local identities so shared occurrences reuse inference.
  let parent := context.pop
  let result ← inBinderContext parent fun locals =>
    buildBinderContext context (fun locals => do
      let lctx ← getQueryLocals
      modify fun s => { s with binderContexts := s.binderContexts.insert context (lctx, locals) }
      k locals) parent.size locals
  return result.join

-- The syntax scan checks TERM occurrences inside types. They are not themselves
-- assumed to be types (e.g. Classical constants on either side of an equality).
def typeMentions (env : CompiledView) (e : Expr) : WalkM Bool := do
  unless ← chargeSummaryWork (fun c => { c with recheckedNodes := c.recheckedNodes + 1 }) do return false
  if let .const n _ := e.getAppFn then directConstant env n
  if let .proj n _ _ := e.getAppFn then directProjection env n
  return ← compareCanonical e (← get).statement

-- The least unfinished ancestor used by a recursive cutoff. None means that
-- no enclosing-family assumption was used; this is proof-dependency metadata,
-- never a classification mode.
def mergeAssumptions (a b : Option Nat) : Option Nat :=
  match a, b with
  | none, x | x, none => x
  | some a, some b => some (min a b)

def noteFamilyAssumption (depth : Nat) : WalkM Unit := do
  unless ← chargeTraversal do return
  modify fun s => { s with assumedFamilyDepth := mergeAssumptions s.assumedFamilyDepth (some depth) }

def checkedStatementType (env : CompiledView) (type : Expr) :
    WalkM (Option ProvenanceAdmissionWitness) := do
  unless ← chargeTraversal do return none
  -- admission-exit: checkedStatementType.1 rule=retained-witness.rule
  if let some evidence := (← get).apartPropositions[type]? then return some evidence
  modify fun s => { s with identityUnknown := none }
  let state ← get
  let statement := state.statement
  let evidence ← do
    let some (some left) ← boundedQuery (exactNodeHead? type) `statement_exact_left
      | return none
    let some (some right) ← boundedQuery (exactNodeHead? statement) `statement_exact_right
      | return none
    let some leftName := left.getAppFn.constName? | return none
    let some rightName := right.getAppFn.constName? | return none
    let some (.inductInfo _) := env.find? leftName | return none
    let some (.inductInfo _) := env.find? rightName | return none
    unless leftName != rightName do return none
    return some (witness .statementHeadApart left)
  if evidence.isNone && !(← get).identityFailureTraced then
    modify fun s => { s with identityFailureTraced := true }
    auditTrace s!
      "statement_identity_unresolved first={(← get).currentFirst} site={(← get).currentOrigin} type={type} registered={(← get).statement}"
  if let some evidence := evidence then
    if !type.hasLooseBVars && !type.hasMVar && !type.hasLevelMVar then
      modify fun s => { s with apartPropositions := s.apartPropositions.insert type evidence }
  -- admission-exit: checkedStatementType.2 rule=retained-witness.rule
  return evidence


end LeanInformationAudit.RegistrationGates

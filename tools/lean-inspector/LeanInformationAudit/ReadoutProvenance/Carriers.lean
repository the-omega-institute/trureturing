import LeanInformationAudit.ReadoutProvenance.State
namespace LeanInformationAudit.RegistrationGates
open Lean

partial def aliasBody (value : Expr) (args : Array Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  if args.isEmpty then return some value
  match value with
  | .lam _ _ body _ =>
    let some body ← substitute body #[args[0]!] | return none
    aliasBody body (args.extract 1 args.size)
  | .mdata _ body => aliasBody body args
  | _ =>
    unless ← chargeTraversal args.size do return none
    return some (mkAppN value args)

partial def representationType (type : Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  match type with
  | .mdata _ body => representationType body
  | .fvar id =>
    let some value := (← id.getDecl).value? (allowNondep := true) | return some type
    representationType value
  | _ => return some type

-- A field role needs a positive spelling: kind alone cannot distinguish a
-- carrier slot from an ordinary value. Explicit aliases are followed before
-- deciding the role; no recursor or opaque carrier is evaluated. These witnesses
-- discharge only the role check. observedType still checks all parameters,
-- proof identities and nominal fields of the recognized value type.
partial def nominalFieldShape (env : Environment) (type : Expr)
    (parameters : Array Expr) : WalkM (Option ProvenanceAdmissionWitness) := do
  let some concrete ← representationType type | return none
  let some kind ← occurrenceType concrete | return none
  if kind == .sort .zero then
    -- admission-exit: nominalFieldShape.1 rule=fieldProposition
    return some (witness .fieldProposition concrete)
  match concrete with
  | .sort _ => return none
  | .forallE n domain body bi =>
    let result ← Meta.withLocalDecl n bi domain fun x => do
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
      let value ← Core.instantiateValueLevelParams declaration levels (allowOpaque := false)
      let some body ← aliasBody value args | return none
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
    namespaceLabel (← getEnv) name, (← get).theoremName⟩

def statementStep (env : Environment) (current : Expr) : WalkM StatementStep := do
  let some (head, args) ← applicationParts current | return .incomplete
  match head with
  -- admission-exit: statementStep.1 rule=statementForall
  | .forallE .. => return .recognized (witness .statementForall current)
  | .const n levels =>
    match env.find? n with
    -- admission-exit: statementStep.2 rule=statementInductive
    | some (.inductInfo _) => return .recognized (witness .statementInductive current)
    | some (.defnInfo info) =>
      let value ← Core.instantiateValueLevelParams (.defnInfo info) levels
      let some body ← aliasBody value args | return .incomplete
      return .next body
    | _ => return ← statementUnknown head
  | .lam .. =>
    if args.isEmpty then return ← statementUnknown head
    let some body ← aliasBody head args | return .incomplete
    return .next body
  | .mdata _ body => return .next (mkAppN body args)
  | .letE _ _ value body _ =>
    let some body ← substitute body #[value] | return .incomplete
    let some body ← aliasBody body args | return .incomplete
    return .next body
  | .proj structureName index receiver =>
    let (record, work) := ReadoutFamily.carrier env receiver (← get).exprFuel
    unless ← chargeTraversal work do return .incomplete
    let some record := record | return ← statementUnknown head
    let some (ctor, fields) ← applicationParts record | return .incomplete
    let some (.ctorInfo info) := ctor.constName?.bind env.find?
      | return ← statementUnknown head
    unless info.induct == structureName do return ← statementUnknown head
    let some field := fields[info.numParams + index]? | return ← statementUnknown head
    let some body ← aliasBody field args | return .incomplete
    return .next body
  | _ => return ← statementUnknown head

private partial def statementOuter (env : Environment) (type : Expr) :
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
partial def listStatementBoundary (env : Environment) (type : Expr)
    (binders : Nat := 0) : WalkM (Option ProvenanceAdmissionWitness) := do
  let some evidence ← statementOuter env type | return none
  let type := evidence.matchedType
  match type with
  | .forallE n domain body bi =>
    if binders == 0 then
      let some firstProof ← boundedMeta (Meta.isProp domain) `list_statement_domain | return none
      if !firstProof then
        let twoDataBinders ← Meta.withLocalDecl n bi domain fun x => do
          let some body ← substitute body #[x] | return false
          let some evidence ← statementOuter env body | return false
          let body := evidence.matchedType
          let .forallE _ secondDomain _ _ := body | return false
          let some secondProof ← boundedMeta (Meta.isProp secondDomain) `list_statement_domain
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
    Meta.withLocalDecl n bi domain fun x => do
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
partial def dataCarrier (env : Environment) (type : Expr)
    (active : Array Expr := #[]) : WalkM (Option ProvenanceAdmissionWitness) := do
  unless ← chargeTraversal do return none
  let some type ← representationType type | return none
  let some kind ← occurrenceType type | return none
  let .sort level := kind | return none
  unless level.isNeverZero do return none
  match type with
  | .sort _ => return none
  | .fvar id =>
    if (← id.getDecl).value? (allowNondep := true) |>.isNone then
      -- admission-exit: dataCarrier.1 rule=rigidCarrier
      return some (witness .rigidCarrier type)
    return none
  | .proj structureName index receiver =>
    -- Only registered arena/signature carrier selectors inherit the rigid
    -- local parameter boundary. Concrete receivers expose their actual field,
    -- which must pass the same carrier test (including Prop/payload fences).
    let audited := ReadoutFamily.carrierHeads.any fun selector =>
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
      if (← id.getDecl).value? (allowNondep := true) |>.isNone then
        -- admission-exit: dataCarrier.2 rule=carrierProjection
        return some (witness .carrierProjection type)
    let .next field ← statementStep env (.proj structureName index receiver) | return none
    if field == type then return none
    -- admission-exit: dataCarrier.forward.1 rule=retained-witness.rule
    dataCarrier env field active
  | .forallE n domain body bi =>
    unless (← dataCarrier env domain active).isSome do return none
    Meta.withLocalDecl n bi domain fun x => do
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
      let value ← Core.instantiateValueLevelParams (.defnInfo info) levels
      let some body ← aliasBody value args | return none
      -- admission-exit: dataCarrier.6 rule=retained-witness.rule
      return ← dataCarrier env body (active.push type)
    let some branches ← caseFields type | return none
    for (lctx, instances, fields) in branches do
      for field in fields do
        let clean ← Meta.withLCtx lctx instances do
          let some fieldType ← occurrenceType field | return none
          -- admission-exit: dataCarrier.forward.3 rule=retained-witness.rule
          dataCarrier env fieldType (active.push type)
        unless clean.isSome do return none
    -- admission-exit: dataCarrier.7 rule=nominalCarrier
    return some (witness .nominalCarrier type)

-- Record explicit proposition-alias spellings only as rejection witnesses.
-- These hashes never certify non-mention and never normalize data operands.
def statementAliases (env : Environment) : WalkM Unit := do
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

-- The final supported outer spelling is used for structural family fences.
-- Computed operands remain untouched and cannot establish non-mention.
def statementBoundary : WalkM (Option ProvenanceAdmissionWitness) := do
  -- admission-exit: statementBoundary.1 rule=retained-witness.rule
  return (← get).recognizedStatement

-- A carrier alias is supported only when its explicit body is another named
-- type application. This recognizes Unit/PUnit without evaluating data or
-- admitting arbitrary computed carriers. The ordinary type fold still checks
-- every parameter and nominal field before this narrower List boundary is used.
partial def namedCarrier (env : Environment) (type : Expr) : WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  let some type ← representationType type | return none
  let .const name levels := type.getAppFn | return some type
  let some (.defnInfo info) := env.find? name | return some type
  let value ← Core.instantiateValueLevelParams (.defnInfo info) levels
  let some body ← aliasBody value type.getAppArgs | return none
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
      Meta.withLocalDecl n bi t fun x => next (locals.push x)
    | .letE n t v _ nd =>
      let some t ← substitute t locals | return none
      let some v ← substitute v locals | return none
      Meta.withLetDecl n t v (fun _ => next (locals.push v)) (nondep := nd)
    | _ =>
      noteUnclassified ⟨"unclassified_binder_context", `binder, "unclassified", `binder⟩
      return none
  else return some (← k locals)

-- Reuse reconstructed binders only when the original parent context is empty.
-- Restoring both locals and local instances preserves their actual types and
-- stable fvar identities; nested callers retain their existing parent context.
partial def inBinderContext (context : Array Expr) (k : Array Expr → WalkM α) :
    WalkM (Option α) := do
  if context.isEmpty then return some (← k #[])
  if !(← getLCtx).isEmpty then return ← buildBinderContext context k
  unless ← chargeTraversal (2 * context.size + 1) do return none
  if let some (lctx, instances, locals) := (← get).binderContexts[context]? then
    return some (← Meta.withLCtx lctx instances (k locals))
  unless ← chargeTraversal context.size do return none
  -- Canonicalize the parent first: extending a lexical prefix must retain
  -- its immutable local identities so shared occurrences reuse inference.
  let parent := context.pop
  let result ← inBinderContext parent fun locals =>
    buildBinderContext context (fun locals => do
      let lctx ← getLCtx
      let instances ← Meta.getLocalInstances
      modify fun s => { s with binderContexts := s.binderContexts.insert context (lctx, instances, locals) }
      k locals) parent.size locals
  return result.join

-- The syntax scan checks TERM occurrences inside types. They are not themselves
-- assumed to be types (e.g. Classical constants on either side of an equality).
def typeMentions (env : Environment) (e : Expr) : WalkM Bool := do
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

-- A hash mismatch never proves that two propositions have different statement
-- identities. This bounded recognizer establishes an actual rigid distinction:
-- different kernel heads, literals, domains, or a distinguishing live argument.
-- Unknown/computed heads stop. It never evaluates a recursor or proof term.
private partial def rigidStatementLocal (expression : Expr) : WalkM Bool := do
  unless ← chargeTraversal do return false
  match expression with
  | .fvar id => return ((← id.getDecl).value? (allowNondep := true)).isNone
  | .proj _ _ receiver => rigidStatementLocal receiver
  | .app function _ => rigidStatementLocal function
  | _ => return false

private partial def statementIdentityForm (env : Environment) (expression : Expr) :
    WalkM (Option Expr) := do
  unless ← chargeTraversal do return none
  let some expression ← representationType expression | return none
  let some (head, args) ← applicationParts expression | return none
  if let .fvar id := head then
    if let some value := (← id.getDecl).value? (allowNondep := true) then
      let some body ← aliasBody value args | return none
      return ← statementIdentityForm env body
    return some expression
  if let .proj structureName index receiver := head then
    -- A projection chain from an unassigned local record is rigid. A concrete
    -- receiver still follows the audited constructor-field decoder below.
    if let some localReceiver ← statementIdentityForm env receiver then
      if ← rigidStatementLocal localReceiver then
        return some (mkAppN (.proj structureName index localReceiver) args)
  match expression with
  | .sort _ | .lit _ | .lam .. => return some expression
  | _ => pure ()
  -- These quotient predicates have fixed proposition families after every
  -- possible reduction: List.Pairwise and List.Mem respectively. They do not
  -- expose an arbitrary proposition chosen by a carrier or callback.
  if #[`Multiset.Nodup, `Multiset.Mem].contains (head.constName?.getD Name.anonymous) then
    return some expression
  if (naturalLiteral expression).isSome ||
      expression.isConstOf ``Bool.true || expression.isConstOf ``Bool.false then
    return some expression
  if let .const name _ := head then
    if (env.find? name).any (fun info => match info with
        | .ctorInfo c => c.induct == ``Nat
        | _ => false) then return some expression
  match ← statementStep env expression with
  | .recognized evidence => return some evidence.matchedType
  | .next next => statementIdentityForm env next
  | .unclassified site =>
    if (← get).identityUnknown.isNone then modify fun s => { s with identityUnknown := some site }
    return none
  | .incomplete => noteIncomplete `incomplete_classification `statement_identity; return none

private partial def statementApart (env : Environment) (left right : Expr) :
    WalkM (Option ProvenanceAdmissionWitness) := do
  unless ← chargeTraversal do return none
  -- Equal fingerprints include possible collisions, so they never admit.
  if hash left == hash right then return none
  let some a ← statementIdentityForm env left | return none
  let some b ← statementIdentityForm env right | return none
  if hash a == hash b then return none
  if let some x := naturalLiteral a then
    if let some y := naturalLiteral b then
      if x != y then
        -- admission-exit: statementApart.1 rule=statementLiteralApart
        return some (witness .statementLiteralApart a)
  if (a.isConstOf ``Bool.true && b.isConstOf ``Bool.false) ||
      (a.isConstOf ``Bool.false && b.isConstOf ``Bool.true) then
    -- admission-exit: statementApart.2 rule=statementLiteralApart
    return some (witness .statementLiteralApart a)
  if let .lit x := a then
    if let .lit y := b then
      -- admission-exit: statementApart.3 rule=statementLiteralApart
      if x != y then return some (witness .statementLiteralApart a)
  let kernelHead := fun expression => expression.getAppFn.constName?.filter fun name =>
    (env.find? name).any fun info => match info with
      | .inductInfo _ => true
      | .ctorInfo c => c.induct == ``Nat
      | _ => false
  let metadataFamily := fun e =>
    if e.getAppFn.isConstOf `Multiset.Nodup then some ``List.Pairwise
    else if e.getAppFn.isConstOf `Multiset.Mem then some ``List.Mem else none
  let am := metadataFamily a
  let bm := metadataFamily b
  let ah := am.orElse fun _ => kernelHead a
  let bh := bm.orElse fun _ => kernelHead b
  if let some an := ah then
    if let some bn := bh then
      if an != bn then
        -- admission-exit: statementApart.4 rule=statementMetadataApart
        if am.isSome || bm.isSome then return some (witness .statementMetadataApart a)
        -- admission-exit: statementApart.5 rule=statementHeadApart
        return some (witness .statementHeadApart a)
      -- A shared metadata family is not evidence of identity or disjointness;
      -- its quotient representation is deliberately left unresolved.
      if am.isSome || bm.isSome then return none
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      unless aa.size == ba.size do return none
      unless ← chargeTraversal aa.size do return none
      for i in [:aa.size] do
        if (← statementApart env aa[i]! ba[i]!).isSome then
          -- admission-exit: statementApart.6 rule=statementArgumentApart
          return some (witness .statementArgumentApart a)
      return none
  -- A rigid type parameter cannot reduce to a kernel inductive type head.
  -- No distinct-proof-variable or proof-constructor comparison is permitted.
  let rigidValue := fun e h => h.isSome || e.isForall || e.isSort ||
    (naturalLiteral e).isSome || e.isConstOf ``Bool.true || e.isConstOf ``Bool.false
  let an ← rigidStatementLocal a.getAppFn
  let bn ← rigidStatementLocal b.getAppFn
  if (an && rigidValue b bh) || (bn && rigidValue a ah) then
    -- admission-exit: statementApart.7 rule=statementRigidApart
    return some (witness .statementRigidApart a)
  match a, b with
  | .forallE n da ab bi, .forallE _ db bb _
  | .lam n da ab bi, .lam _ db bb _ =>
    if (← statementApart env da db).isSome then
      -- admission-exit: statementApart.8 rule=statementDomainApart
      return some (witness .statementDomainApart a)
    -- Congruence is conditional on equal domains. In that case one shared
    -- binder gives both well-typed bodies; unequal domains already distinguish
    -- the binders. This does not decide domain equality or normalize a carrier.
    Meta.withLocalDecl n bi da fun x => do
      let some ab ← substitute ab #[x] | return none
      let some bb ← substitute bb #[x] | return none
      if (← statementApart env ab bb).isSome then
        -- admission-exit: statementApart.9 rule=statementBodyApart
        return some (witness .statementBodyApart a)
      return none
  | .forallE .., _ =>
    -- admission-exit: statementApart.10 rule=statementMetadataApart
    if bm.isSome then return some (witness .statementMetadataApart a)
    -- admission-exit: statementApart.11 rule=statementHeadApart
    if bh.isSome || b.isSort then return some (witness .statementHeadApart a)
    return none
  | _, .forallE .. =>
    -- admission-exit: statementApart.12 rule=statementMetadataApart
    if am.isSome then return some (witness .statementMetadataApart a)
    -- admission-exit: statementApart.13 rule=statementHeadApart
    if ah.isSome || a.isSort then return some (witness .statementHeadApart a)
    return none
  | .sort .zero, .sort (.succ _) | .sort (.succ _), .sort .zero =>
    -- admission-exit: statementApart.14 rule=statementHeadApart
    return some (witness .statementHeadApart a)
  | .sort _, _ =>
    -- admission-exit: statementApart.15 rule=statementHeadApart
    if bh.isSome || b.isFVar then return some (witness .statementHeadApart a)
    return none
  | _, .sort _ =>
    -- admission-exit: statementApart.16 rule=statementHeadApart
    if ah.isSome || a.isFVar then return some (witness .statementHeadApart a)
    return none
  | _, _ => return none

def checkedStatementType (env : Environment) (type : Expr) :
    WalkM (Option ProvenanceAdmissionWitness) := do
  unless ← chargeTraversal do return none
  -- admission-exit: checkedStatementType.1 rule=retained-witness.rule
  if let some evidence := (← get).apartPropositions[type]? then return some evidence
  modify fun s => { s with identityUnknown := none }
  let evidence ← statementApart env type (← get).statement
  if evidence.isNone then
    if let some site := (← get).identityUnknown then noteUnclassified site
  if evidence.isNone && !(← get).identityFailureTraced then
    modify fun s => { s with identityFailureTraced := true }
    trace[InformationProvenance.check]
      "statement_identity_unresolved first={(← get).currentFirst} site={(← get).currentOrigin} type={type} registered={(← get).statement}"
  if let some evidence := evidence then
    if !type.hasLooseBVars && !type.hasMVar && !type.hasLevelMVar then
      modify fun s => { s with apartPropositions := s.apartPropositions.insert type evidence }
  -- admission-exit: checkedStatementType.2 rule=retained-witness.rule
  return evidence


end LeanInformationAudit.RegistrationGates

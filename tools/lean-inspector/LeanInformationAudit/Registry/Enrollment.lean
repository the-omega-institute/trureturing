import LeanInformationAudit.Registry.Evidence

namespace LeanInformationAudit.TemplateAudit
open Lean Meta

/-- A byte-radix tree. Each node has at most 256 sorted outgoing byte edges;
lookup visits only the selected key's path, never the collection of templates. -/
inductive TemplateTrie where
  | node (value : Option TemplatePlanData) (edges : Array (UInt8 × TemplateTrie))
  deriving Inhabited

namespace TemplateTrie
private partial def insertAt (tree : TemplateTrie) (key : ByteArray) (offset : Nat)
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
private partial def lookupAt [Monad m] (tree : TemplateTrie) (key : ByteArray)
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

/-- The only persistent enrollment entry: byte buffers and a fixed digest.
No decoded expression, plan, universe list or dependency graph is deserialized
by Lean on behalf of this extension. Lean's general olean loading is separate. -/
structure TemplatePlanFrame where
  key : ByteArray
  payload : ByteArray
  identity : String
  deriving Inhabited

def TemplatePlanFrame.retainedBytes (frame : TemplatePlanFrame) : Nat :=
  frame.key.size + frame.payload.size + frame.identity.utf8ByteSize + 16

structure TemplateIndex where
  private trie : TemplateTrie := .node none #[]
  bytes : Nat := 0
  error : Option String := none
  decodeAttempts : Nat := 0
  decodedAllocationBytes : Nat := 0
  private localFrames : Array TemplatePlanFrame := #[]
  deriving Inhabited

private def TemplateIndex.insertChecked (index : TemplateIndex) (plan : TemplatePlanData)
    (retained : Nat) : TemplateIndex := Id.run do
  let key := plan.name.toString.toUTF8
  let duplicate := (TemplateTrie.lookupAt index.trie key 0 (pure () : Id Unit)).isSome
  if duplicate then return { index with error := some "unclassified_form:E7.duplicate_enrollment" }
  return { index with
    trie := TemplateTrie.insertAt index.trie key 0 plan
    bytes := index.bytes + retained }

/-- Both limits are checked before decoding or allocating a single plan node.
After the first failure, the importer stops consuming the remaining stream. -/
def TemplateIndex.addFrame (index : TemplateIndex) (frame : TemplatePlanFrame)
    (env : Environment) (importOwner : Name) : TemplateIndex := Id.run do
  if index.error.isSome then return index
  if frame.key.size == 0 || frame.key.size > 1024 || frame.payload.size == 0 ||
      frame.identity.utf8ByteSize != 64 || frame.retainedBytes > 65536 then
    return { index with error := some "incomplete_closure:E8.import_framing" }
  if index.bytes + frame.retainedBytes > 8388608 then
    return { index with error := some "incomplete_closure:E8.import_bytes" }
  unless Sha256.hex frame.payload == frame.identity do
    return { index with error := some "incomplete_closure:E7.import_identity" }
  let index := { index with decodeAttempts := index.decodeAttempts + 1 }
  let .ok (decoded, allocated) := PlanDecoder.decode frame.payload (32 * frame.payload.size)
    | return { index with error := some "incomplete_closure:E7.import_encoding" }
  let plan := { decoded with planIdentity := frame.identity }
  if plan.name.isAnonymous || plan.definitionOwner.isAnonymous || plan.enrollmentOwner.isAnonymous ||
      plan.name.toString.toUTF8 != frame.key || plan.compiler != Lean.versionString ||
      plan.toolchain != Lean.versionString then
    return { index with error := some "incomplete_closure:E8.import_framing" }
  let actualOwner := (RegistrationReifier.declaringModuleOf env plan.name).getD env.header.mainModule
  unless env.contains plan.name && plan.enrollmentOwner == importOwner &&
      plan.definitionOwner == actualOwner do
    return { index with error := some "incomplete_closure:E7.import_owner" }
  return { (index.insertChecked plan frame.retainedBytes) with
    decodedAllocationBytes := index.decodedAllocationBytes + allocated }

def TemplateIndex.lookup [Monad m] (index : TemplateIndex) (name : Name)
    (observe : m Unit) : m (Except String TemplatePlanData) := do
  if let some error := index.error then return .error error
  let key := name.toString.toUTF8
  if key.size > 1024 then return .error "incomplete_closure:E8.name_bytes"
  match ← TemplateTrie.lookupAt index.trie key 0 observe with
  | some plan => return .ok plan
  | none => return .error "unclassified_form:dtr.unregistered_template"

private structure CheckedTemplatePlan where
  data : TemplatePlanData
  frame : TemplatePlanFrame

private initialize templateIndexExt : PersistentEnvExtension TemplatePlanFrame CheckedTemplatePlan TemplateIndex ←
  registerPersistentEnvExtension {
    -- A new entry layout must not reinterpret an old olean extension payload.
    name := `LeanInformationAudit.TemplateAudit.checkedPlanFramesV5
    mkInitial := pure {}
    addEntryFn := fun index checked =>
      { (index.insertChecked checked.data checked.frame.retainedBytes) with
        localFrames := index.localFrames.push checked.frame }
    addImportedFn := fun modules => do
      let env := (← read).env
      let mut index : TemplateIndex := {}
      for i in [:modules.size] do
        if index.error.isSome then break
        let some owner := env.header.moduleNames[i]? | return { index with error := some "incomplete_closure:E7.import_owner" }
        for frame in modules[i]! do
          if index.error.isSome then break
          index := index.addFrame frame env owner
      return index
    exportEntriesFn := fun index => index.localFrames
  }

/-- Read-only observation of actual query operations in the environment's
imported index. The observer cannot supply a plan or affect admission. -/
def observeSelectedPlan [Monad m] (env : Environment) (name : Name)
    (observe : m Unit) : m (Except String TemplatePlanData) :=
  (templateIndexExt.getState env).lookup name observe

/-- Imported checked summaries are the sole lookup source. -/
def selectedPlan (env : Environment) (name : Name) : Except String TemplatePlanData :=
  observeSelectedPlan env name (pure () : Id Unit)

/-- Serialized bytes retained by the actual imported index, including keys. -/
def importedSummaryBytes (env : Environment) : Nat := (templateIndexExt.getState env).bytes

end LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.TemplateAudit
open Lean Meta

private structure CompileState where
  remaining : Nat := 524288
  identityState : Option RegistrationGates.WalkState := none
  dependencies : Array DependencyIdentity := #[]
  rules : Array String := #[]
  constructorTypes : NameSet := {}
  /-- Only original AST parameters and direct constructor fields carry descent
  authority. An arbitrary local with the same type does not. -/
  astVariables : FVarIdSet := {}

private abbrev CompileM := StateT CompileState MetaM

private def charge (work : Nat := 1) : CompileM Unit := do
  Core.checkMaxHeartbeats "template construction"
  unless work ≤ (← get).remaining do throwError "incomplete_closure:E8.work"
  modify fun s => { s with remaining := s.remaining - work }

/-- Pure construction shares the caller's remaining quota. The transformer
fails before allocation when its quota or structural depth is exhausted. -/
private def construct (action : Nat → Except String (α × Nat)) : CompileM α := do
  let (result, work) ← match action (← get).remaining with
    | .ok value => pure value
    | .error reason => throwError reason
  charge work
  return result

private def eraseInput (e : Expr) : CompileM Expr := do
  let (erased, work) ← eraseProofs e (← get).remaining
  charge work
  return erased

private def instantiate (body argument : Expr) : CompileM Expr :=
  construct (fun fuel => PlanTransform.substituteExpr body argument 0 fuel)

private def abstractPlan (body : PlanNode) (x : Expr) : CompileM PlanNode :=
  construct (fun fuel => PlanTransform.abstractPlan body x.fvarId! fuel)

private partial def sameLevel (a b : Level) : CompileM Bool := do
  charge
  match a, b with
  | .zero, .zero => return true
  | .param a, .param b => return a == b
  | .succ a, .succ b => sameLevel a b
  | .max a b, .max c d | .imax a b, .imax c d =>
    return (← sameLevel a c) && (← sameLevel b d)
  | _, _ => return false

private partial def sameRaw (a b : Expr) : CompileM Bool := do
  charge
  if hash a != hash b then return false
  match a, b with
  | .bvar a, .bvar b => return a == b
  | .fvar a, .fvar b => return a == b
  | .sort a, .sort b => sameLevel a b
  | .const a us, .const b vs =>
    if a != b || us.length != vs.length then return false
    for (u, v) in us.zip vs do unless ← sameLevel u v do return false
    return true
  | .lit a, .lit b => return a == b
  | .app f a, .app g b => return (← sameRaw f g) && (← sameRaw a b)
  | .lam n t b bi, .lam m u c ci | .forallE n t b bi, .forallE m u c ci =>
    return n == m && bi == ci && (← sameRaw t u) && (← sameRaw b c)
  | .letE n t v b nd, .letE m u w c md =>
    return n == m && nd == md && (← sameRaw t u) && (← sameRaw v w) && (← sameRaw b c)
  | .proj n i b, .proj m j c => return n == m && i == j && (← sameRaw b c)
  -- Metadata never receives a deduplication shortcut; it remains retained.
  | _, _ => return false

private partial def samePlan (a b : PlanNode) : CompileM Bool := do
  charge
  match a, b with
  | .atom a, .atom b => sameRaw a b
  | .typeNode a, .typeNode b => samePlan a b
  | .proofLeaf t, .proofLeaf u => sameRaw t u
  | .expanded a p, .expanded b q => return (← sameRaw a b) && (← samePlan p q)
  | .app a b, .app c d | .audit a b, .audit c d =>
    return (← samePlan a c) && (← samePlan b d)
  | .lam t b bi, .lam u c ci | .forallE t b bi, .forallE u c ci =>
    return bi == ci && (← samePlan t u) && (← samePlan b c)
  | .letE t v b nd, .letE u w c md =>
    return nd == md && (← samePlan t u) && (← samePlan v w) && (← samePlan b c)
  | .proj n i b, .proj m j c => return n == m && i == j && (← samePlan b c)
  | _, _ => return false

/-- An identical checked subtree already carries the same obligations. Search
only nodes visited without prior substitution, never raw expansion/proof syntax.
Inputs have no loose variables at this compilation boundary; external locals
keep their unique fvar identities. Every search/comparison step is charged. -/
private partial def containsInput (tree input : PlanNode) : CompileM Bool := do
  charge
  if ← samePlan tree input then return true
  let child := fun p => containsInput p input
  let rec arguments : PlanNode → CompileM Bool
    | .app f a => do
      charge
      if ← child a then return true
      arguments f
    | _ => pure false
  match tree with
  | .audit a b | .lam a b _ | .forallE a b _ =>
    return (← child a) || (← child b)
  -- A function or let body can change context before its obligations are read.
  | .app .. => arguments tree
  | .letE t v _ _ => return (← child t) || (← child v)
  | .expanded _ b | .typeNode b | .mdata _ b | .proj _ _ b => child b
  | _ => return false

private def rule (name : String) : CompileM Unit := do
  charge
  unless (← get).rules.contains name do
    modify fun s => { s with rules := s.rules.push name }

private def binder (name : Name) (bi : BinderInfo) (type : Expr)
    (body : Expr → CompileM α) : CompileM α := fun state =>
  withLocalDecl name bi type fun x => (body x).run state

private def ownerOf (env : Environment) (name : Name) : Option Name :=
  if env.contains name then
    some ((RegistrationReifier.declaringModuleOf env name).getD env.header.mainModule)
  else none

private def dependency (info : ConstantInfo) : CompileM Unit := do
  let state ← get
  if state.dependencies.any (·.name == info.name) then return
  if state.dependencies.size ≥ 4096 then throwError "incomplete_closure:E8.definition_constants"
  let some owner := ownerOf (← getEnv) info.name | throwError "incomplete_closure:E7.owner"
  let .ok (typeId, typeBytes) ← rawIdentity info.levelParams info.type state.remaining
    | throwError "incomplete_closure:E7.type_identity"
  charge typeBytes
  let (bodyId, bodyBytes) ← if ← isProp info.type then pure ("", 0) else match info.value? with
    | some body =>
      let .ok pair ← rawIdentity info.levelParams body (← get).remaining
        | throwError "incomplete_closure:E7.body_identity"
      pure pair
    | none => pure ("", 0)
  charge bodyBytes
  modify fun s => { s with dependencies := s.dependencies.push {
    name := info.name, owner, typeIdentity := typeId, bodyIdentity := bodyId } }

-- These names describe the finite grammar, never individual template families.
private def interfaceTypes : Array Name := #[
  `D5.S3.ConceptDynamics.InformationEscape.Arena,
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveSignature,
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization,
  `D5.S3.ConceptDynamics.CIRPT.PrimitiveAxis,
  `D5.S3.ConceptDynamics.InformationEscape.StructuralArena,
  `LeanInformationAudit.StructuralPrimitiveSignature,
  `LeanInformationAudit.StructuralPrimitiveRealization]

private def dataTypes : Array Name :=
  #[`Unit, `PUnit, `Bool, `Nat, `Fin, `Prod, `Sum, `Option, `Subtype]

private def propTypes : Array Name := #[`Eq, `True, `False, `And, `Or, `Not, `Iff, `Exists, `Nat.lt]
private def dictionaryTypes : Array Name := #[`Fintype, `DecidableEq, `Decidable, `DecidablePred, `DecidableRel]

private def interfaceProjection (env : Environment) (name : Name) : Bool :=
  match env.getProjectionFnInfo? name with
  | some p => interfaceTypes.contains p.ctorName.getPrefix &&
      #["State", "Index", "Output", "AnchorIndex", "indexFintype", "indexDecidableEq",
        "outputDecidableEq", "anchorFintype", "anchorDecidableEq", "axis", "readout", "anchor"].contains
          name.getString!
  | none => false

/-- The checked primitive reference is retained by the judge's own module. It is
not a content callback or an enrollment claim. Every use compares the reflected
Name, universe telescope, raw type/body identities and actual declaring module. -/
private structure PrimitivePin where
  identity : DependencyIdentity
  levelCount : Nat
  deriving Inhabited

private initialize primitivePins : SimplePersistentEnvExtension PrimitivePin (Array PrimitivePin) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun modules => modules.foldl (· ++ ·) #[] }

private def constructiveDictionaryNames : Array Name := #[
  `Unit.fintype, `PUnit.fintype, `Bool.fintype, `Fin.fintype, `instFintypeProd,
  `Sum.instFintype, `Option.instFintype, `Subtype.fintype,
  `instDecidableEqUnit, `instDecidableEqPUnit, `instDecidableEqBool,
  `instDecidableEqFin, `Prod.instDecidableEq, `Sum.instDecidableEq,
  `Option.instDecidableEq, `Subtype.instDecidableEq]

private def checkedDictionary (info : ConstantInfo) : CompileM Bool := do
  unless constructiveDictionaryNames.contains info.name do return false
  let some pin := (primitivePins.getState (← getEnv)).find? (·.identity.name == info.name)
    | throwError "incomplete_closure:E2.dictionary_pin"
  dependency info
  let some current := (← get).dependencies.find? (·.name == info.name)
    | throwError "incomplete_closure:E2.dictionary_identity"
  unless current.owner == pin.identity.owner && current.typeIdentity == pin.identity.typeIdentity &&
      current.bodyIdentity == pin.identity.bodyIdentity && info.levelParams.length == pin.levelCount do
    throwError "unclassified_form:E2.dictionary_identity"
  rule "E2.dictionary"
  return true

private def occurrenceIdentity (e : Expr) : CompileM Unit := do
  let some identity := (← get).identityState | return
  let available := (← get).remaining
  let (_, identity) ← (RegistrationGates.argumentIdentityNode (← getEnv) e).run
    { identity with exprFuel := available }
  charge (available - identity.exprFuel)
  modify fun s => { s with identityState := some identity }
  if identity.incomplete then throwError "incomplete_closure:dtr.argument_audit"
  if identity.forbidden then throwError "forbidden_dependency:dtr.argument_audit"
  if identity.unclassified.isSome then throwError "unclassified_form:E6.argument_identity"

private def staticIdentity (e : Expr) : CompileM Unit := do
  let env ← getEnv
  let name := e.getAppFn.constName?.getD .anonymous
  let projected := match e.getAppFn with
    | .proj typeName _ _ => RegistrationGates.isJudgeProjection typeName
    | _ => false
  if projected || (!name.isAnonymous && (InformationRegistry.hasTheorem env name ||
      isCompanionName name || RegistrationGates.isJudgeIdentity env name)) then
    throwError "forbidden_dependency:E6.registered_identity"
  if #[`Classical.choice, `Classical.propDecidable, `of_decide_eq_true, `Lean.Expr,
      `Lean.Name, `String].contains name then
    throwError "forbidden_dependency:E6.closed_identity"

mutual
private partial def compileExpr (e : Expr) (depth : Nat := 0)
    (typePosition : Bool := false) (templateBinders : Nat := 0) : CompileM PlanNode := do
  let checked ← compileNode e depth typePosition templateBinders
  if ← isType e then
    rule "E7.type_obligation"
    return .typeNode checked
  return checked

private partial def compileNode (e : Expr) (depth : Nat)
    (typePosition : Bool) (templateBinders : Nat) : CompileM PlanNode := do
  charge
  if depth > 256 then throwError "incomplete_closure:E8.depth"
  if e.hasMVar then throwError "incomplete_closure:E7.metavariable"
  -- Prop *values* are erased only after their entire proposition is classified.
  -- A proposition expression itself is not a proof value.
  if (← isProof e) then
    let type ← inferType e
    let checkedType ← compileExpr type (depth + 1) true
    rule "E5.proof_leaf"
    return .audit checkedType (.proofLeaf type)
  occurrenceIdentity e
  staticIdentity e
  let child := fun value => compileExpr value (depth + 1) typePosition
  match e with
  | .fvar _ => rule "E3.variable"; return .atom e
  | .bvar _ => throwError "incomplete_closure:E3.loose_binder"
  | .mvar _ => throwError "incomplete_closure:E7.metavariable"
  | .sort _ => rule "E2.sort"; return .atom e
  | .lit (.natVal _) =>
    unless typePosition do throwError "unclassified_form:E3.nonindex_literal"
    rule "E3.index_literal"; return .atom e
  | .lit (.strVal _) => throwError "unclassified_form:E3.string_literal"
  | .lam n t b bi =>
    let tp ← compileExpr t (depth + 1) true
    rule "E3.lambda"
    binder n bi t fun x => do
      if templateBinders > 0 &&
          (← get).constructorTypes.contains (t.getAppFn.constName?.getD .anonymous) then
        modify fun s => { s with astVariables := s.astVariables.insert x.fvarId! }
      let body ← compileExpr (← instantiate b x) (depth + 1) typePosition (templateBinders - 1)
      return .lam tp (← abstractPlan body x) bi
  | .forallE n t b bi =>
    let tp ← compileExpr t (depth + 1) true
    binder n bi t fun x => do
      let bp ← compileExpr (← instantiate b x) (depth + 1) true
      rule "E2.pi"
      return .forallE tp (← abstractPlan bp x) bi
  | .letE n t v b nd =>
    -- A known raw source is forbidden even when its function type has no E2
    -- rule. This check does not enter the value's implementation or erase it.
    charge
    unless ← isProof v do staticIdentity v
    let tp ← compileExpr t (depth + 1) true
    let vp ← compileExpr v (depth + 1) false
    binder n .default t fun x => do
      let bp ← child (← instantiate b x)
      rule "E3.let"
      return .letE tp vp (← abstractPlan bp x) nd
  | .mdata m b => rule "E3.metadata"; return .mdata m (← child b)
  | .proj n i b =>
    if !(interfaceTypes.contains n || #[`Prod, `Subtype].contains n) &&
        (← get).constructorTypes.contains n && !Lean.isClass (← getEnv) n then
      rule "E3.constructor_projection"
      return .proj n i (← child b)
    unless interfaceTypes.contains n || #[`Prod, `Subtype].contains n do
      throwError "unclassified_form:E3.projection"
    rule "E3.projection"; return .proj n i (← child b)
  | .app .. | .const .. =>
    let head := e.getAppFn
    let args := e.getAppArgs
    if head.isFVar || head.isLambda then
      let mut plan ← child head
      for arg in args do plan := .app plan (← child arg)
      rule "E3.application"
      return plan
    let .const name levels := head | throwError "unclassified_form:E3.application_head"
    let info ← getConstInfo name
    -- Standard Nat order notation is the existing Nat.lt proposition grammar.
    -- No user order dictionary or data-position operation is admitted here.
    if typePosition && name == `LT.lt && args.size == 4 &&
        args[0]!.isConstOf `Nat && args[1]!.isConstOf `instLTNat then
      dependency info
      dependency (← getConstInfo `instLTNat)
      return .expanded e (← compileExpr (mkApp2 (mkConst `Nat.lt) args[2]! args[3]!)
        (depth + 1) true)
    if name == `OfNat.ofNat then
      unless typePosition && args.size == 3 && args[0]!.isConstOf `Nat &&
          args[2]!.isAppOfArity `instOfNatNat 1 && args[2]!.getAppArgs[0]!.equal args[1]! do
        throwError "unclassified_form:E3.index_encoding:OfNat.ofNat"
      dependency info
      dependency (← getConstInfo `instOfNatNat)
      rule "E3.nat_index_encoding"
      return .expanded e (← compileExpr args[1]! (depth + 1) true)
    if info.isUnsafe then throwError "unclassified_form:E1.unsafe_definition"
    let fixedType := dataTypes.contains name || propTypes.contains name ||
      dictionaryTypes.contains name || interfaceTypes.contains name ||
      (← get).constructorTypes.contains name
    let constructorTypes := (← get).constructorTypes
    let fixedCtor := match info with
      | .ctorInfo c => dataTypes.contains c.induct || interfaceTypes.contains c.induct ||
          constructorTypes.contains c.induct
      | _ => false
    -- E4c.enumeration_dispatch: nullary constructors form a finite table;
    -- its major premise needs no structural-descent authority.
    if let .recInfo r := info then
      if constructorTypes.contains (r.all.headD .anonymous) &&
          r.numMotives == 1 && r.numIndices == 0 && r.all.length == 1 &&
          args.size > r.getMajorIdx then
        let .inductInfo ind ← getConstInfo (r.all.headD .anonymous)
          | throwError "unclassified_form:E4c.inductive_description"
        let enumeration ← ind.ctors.allM fun ctorName => do
          let .ctorInfo ctor ← getConstInfo ctorName | return false
          return ctor.numFields == 0
        if enumeration then
          let motive := args[r.numParams]!
          -- Compiled match eta-expands its supplied constant motive. Retain
          -- and check the raw argument below, including these beta redexes.
          unless motive.isLambda && !motive.bindingBody!.headBeta.hasLooseBVar 0 do
            throwError "unclassified_form:E4c.structural_descent"
          rule "E4c.enumeration_dispatch"
          dependency info
          let mut plan := PlanNode.atom head
          for arg in args do plan := .app plan (← child arg)
          return plan
    let recursiveCase := match info with
      | .recInfo r => constructorTypes.contains (r.all.headD .anonymous)
      | _ => false
    if recursiveCase then
      let .recInfo r := info | throwError "unclassified_form:E4c.recursor"
      unless r.numMotives == 1 && r.numIndices == 0 && r.all.length == 1 &&
          args.size > r.getMajorIdx && args[r.getMajorIdx]!.isFVar &&
          (← get).astVariables.contains args[r.getMajorIdx]!.fvarId! do
        throwError "unclassified_form:E4c.structural_descent"
      rule "E4c.constructor_recursion_v1"
      dependency info
      let mut plan := PlanNode.atom head
      for index in [:args.size] do
        let arg := args[index]!
        if index ≥ r.numParams + r.numMotives && index < r.getMajorIdx then
          let some description := r.rules[index - r.numParams - r.numMotives]?
            | throwError "incomplete_closure:E4c.branch_description"
          -- The kernel minor premise has constructor fields first, followed by
          -- induction hypotheses. Only direct AST fields are strict subterms.
          plan := .app plan (← compileBranch arg description.nfields (depth + 1) typePosition)
        else
          plan := .app plan (← child arg)
      return plan
    let fixedCase := match info with
      | .recInfo r => #[`Unit, `PUnit, `Bool, `Option, `Sum, `Prod, `Subtype].contains
          (r.all.headD .anonymous)
      | _ => false
    let fixedProjection := interfaceProjection (← getEnv) name || #[`Prod.fst, `Prod.snd, `Subtype.val].contains name
    let dictionary ← checkedDictionary info
    if fixedType || fixedCtor || fixedCase || recursiveCase || fixedProjection || dictionary || name == `Fin.elim0 then
      dependency info
      let mut plan := PlanNode.atom head
      -- Constructor parameters and indices occur in the result type. Only
      -- implicit such arguments receive type context; explicit values do not.
      let mut telescope := info.type
      for arg in args do
        let implicitIndex := match telescope with
          | .forallE _ _ result bi => fixedCtor && bi.isImplicit && result.getForallBody.hasLooseBVar result.getForallArity
          | _ => false
        plan := .app plan (← compileExpr arg (depth + 1)
          (typePosition || fixedType || implicitIndex || #[`Fin.fintype, `instDecidableEqFin].contains name))
        if let .forallE _ _ tail _ := telescope then telescope ← instantiate tail arg
      rule (if fixedCase then "E4.cases" else if fixedType then "E2.type" else "E3.constructor")
      return plan
    if name == ``decide then
      unless args.size == 2 && args[0]!.hasFVar && args[1]!.hasFVar do
        throwError "unclassified_form:E3.closed_decision"
      let mut plan := PlanNode.atom head
      for arg in args do plan := .app plan (← child arg)
      rule "E3.symbolic_decide"
      return plan
    -- A field may itself be a function: only parameters and self must be
    -- supplied before projecting. E4c descent authority is unchanged.
    if let some p := (← getEnv).getProjectionFnInfo? name then
      if !p.fromClass && (← get).constructorTypes.contains p.ctorName.getPrefix &&
          args.size > p.numParams then
        dependency info
        let mut plan := PlanNode.proj p.ctorName.getPrefix p.i (← child args[p.numParams]!)
        for arg in args.extract (p.numParams + 1) args.size do
          plan := .app plan (← child arg)
        rule "E3.constructor_projection"
        return plan
    match info with
    | .thmInfo _ => throwError "forbidden_dependency:E6.executable_theorem:{name}"
    | .recInfo _ => throwError "unclassified_form:E4.recursion:{name}"
    | .defnInfo defn =>
      -- The fixed E2 proposition constructors were handled above. A closed
      -- proposition name cannot acquire a rule by spelling an admitted formula
      -- in its body, even if that body is available and reducible.
      if (← isProp e) && !e.hasFVar then
        throwError "unclassified_form:E2.closed_proposition"
      -- Nesting independent calls is not a definition dependency cycle. Lean's
      -- declaration metadata identifies source recursion before substitution.
      if (← isRecursiveDefinition name) || defn.all.length > 1 then
        throwError "unclassified_form:E5.recursive_definition"
      dependency info
      -- Check every raw argument before capture-avoiding expansion, including
      -- arguments unused by the definition body.
      let mut inputs ← args.mapM child
      let erasedValue ← eraseInput defn.value
      let mut value ← construct (fun fuel => PlanTransform.instantiateExpr erasedValue defn.levelParams levels fuel)
      let erasedType ← eraseInput defn.type
      let mut type ← construct (fun fuel => PlanTransform.instantiateExpr erasedType defn.levelParams levels fuel)
      for arg in args do
        let .lam _ bodyDomain body _ := value
          | throwError "unclassified_form:E5.unsaturated_definition:{name}"
        let .forallE _ domain tail _ := type
          | throwError "unclassified_form:E5.unsaturated_definition:{name}"
        inputs := inputs.push (← compileExpr domain (depth + 1) true)
        inputs := inputs.push (← compileExpr bodyDomain (depth + 1) true)
        charge
        type ← instantiate tail arg
        value ← instantiate body arg
      if value.isLambda then throwError "unclassified_form:E5.unsaturated_definition:{name}"
      inputs := inputs.push (← compileExpr type (depth + 1) true)
      let mut plan ← child value
      for input in inputs.reverse do
        unless ← containsInput plan input do plan := .audit input plan
      rule "E5.definition"
      return .expanded e plan
    | .opaqueInfo _ => throwError "unclassified_form:E5.opaque_definition"
    | _ => throwError "unclassified_form:E2.unknown_constant:{name}"

private partial def compileBranch (expression : Expr) (fields depth : Nat)
    (typePosition : Bool) : CompileM PlanNode := do
  if fields == 0 then return ← compileExpr expression depth typePosition
  charge
  if depth > 256 then throwError "incomplete_closure:E8.depth"
  let .lam n type body bi := expression
    | throwError "unclassified_form:E4c.branch_lambda"
  let domain ← compileExpr type (depth + 1) true
  binder n bi type fun x => do
    if (← get).constructorTypes.contains (type.getAppFn.constName?.getD .anonymous) then
      modify fun s => { s with astVariables := s.astVariables.insert x.fvarId! }
    let checked ← compileBranch (← instantiate body x) (fields - 1) (depth + 1) typePosition
    return .lam domain (← abstractPlan checked x) bi
end

end LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.TemplateAudit
open Lean Meta Elab Command

-- Capture standard dictionary references in the trusted judge module, following
-- P1's reflected-provider pattern. An unavailable pin stays unavailable; import
-- of an arbitrary same-typed instance cannot supply one later.
def initializeGrammarPins : CommandElabM Unit := do
  unless (← getEnv).header.mainModule == `LeanInformationAudit.Syntax do
    throwError "incomplete_closure:E2.pin_producer_owner"
  for name in constructiveDictionaryNames do
    if let some info := (← getEnv).find? name then
      let some owner := ownerOf (← getEnv) name | throwError "DTR primitive owner missing"
      let .ok (typeId, _) ← liftTermElabM <| rawIdentity info.levelParams info.type
        | throwError "DTR primitive type exceeds identity bound: {name}"
      let .ok (bodyId, _) ← liftTermElabM <| rawIdentity info.levelParams (info.value?.getD info.type)
        | throwError "DTR primitive body exceeds identity bound: {name}"
      modifyEnv fun env => primitivePins.addEntry env {
        identity := { name, owner, typeIdentity := typeId, bodyIdentity := bodyId }
        levelCount := info.levelParams.length }

private partial def checkTelescope (type : Expr) (depth : Nat := 0) : CompileM (Array Slot) := do
  if depth > 64 then throwError "incomplete_closure:E8.slots"
  match type with
  | .forallE n domain body bi =>
    if domain == mkSort .zero then throwError "unclassified_form:E1.proposition_slot"
    if bi == .instImplicit && !domain.isForall &&
        !dictionaryTypes.contains (domain.getAppFn.constName?.getD .anonymous) then
      throwError "unclassified_form:E1.instance_slot"
    let _ ← compileExpr domain 0 true
    -- These exact standard aliases describe indexed dictionaries. Classify
    -- their Pi telescope too; an alias must not bypass the family obligation.
    let shape ← if #[`DecidablePred, `DecidableRel].contains
        (domain.getAppFn.constName?.getD .anonymous) then whnf domain else pure domain
    let kind ← match domain with
      | .sort (.succ _) => pure SlotKind.carrier
      | .sort _ => throwError "unclassified_form:E1.carrier_universe"
      | _ =>
        if (← isProp domain) then pure .proof
        else if shape.isForall then
          forallTelescope shape fun fields result => do
            if result.isAppOf `Decidable then
              -- Typing normalization is confined to the dependency test. The
              -- raw domain was checked above and remains in the retained plan.
              -- In particular, a beta/let wrapper cannot manufacture an index.
              let proposition ← whnf result.getAppArgs[0]!
              unless fields.any (fun x => (proposition.find? (· == x)).isSome) do
                throwError "unclassified_form:E1.unindexed_decision_family"
              pure .dictionary
            else pure (if result == mkSort .zero then .predicate else .function)
        else if dictionaryTypes.contains (domain.getAppFn.constName?.getD .anonymous) then
          if domain.isAppOf `Decidable then
            throwError "unclassified_form:E1.closed_decision_slot"
          pure .dictionary
        else if interfaceTypes.contains (domain.getAppFn.constName?.getD .anonymous) then pure .interface
        else pure .data
    if bi == .instImplicit && kind != .dictionary then
      throwError "unclassified_form:E1.instance_slot"
    binder n bi domain fun x => do
      let tail ← checkTelescope (← instantiate body x) (depth + 1)
      -- Stored domains use de Bruijn indices relative to earlier slots.
      let tail ← tail.mapIdxM fun index slot => do
        let type ← construct (fun fuel => PlanTransform.abstractExpr slot.type x.fvarId! index fuel)
        return { slot with type }
      return #[{ kind, binderInfo := bi, type := domain }] ++ tail
  | _ =>
    let name := type.getAppFn.constName?.getD .anonymous
    unless #[`D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization,
        `LeanInformationAudit.StructuralPrimitiveRealization].contains name do
      throwError "unclassified_form:E1.return_interface"
    discard <| compileExpr (← eraseInput type) 0 true
    return #[]

/-- Version 1 permits one non-mutual, unindexed inductive with only direct
strictly positive recursive fields. Nested recursion and function-valued
recursive fields have no rule. The kernel recursor supplies structural descent. -/
private def checkConstructorType (name : Name) : CompileM Unit := do
  let .inductInfo ind ← getConstInfo name
    | throwError "unclassified_form:E4c.inductive_description"
  if ind.all.length != 1 || ind.numIndices != 0 || dataTypes.contains name ||
      ind.isUnsafe || ind.ctors.isEmpty then
    throwError "unclassified_form:E4c.inductive_description"
  forallTelescope ind.type fun _ result => do
    if result == mkSort .zero then throwError "unclassified_form:E4c.proof_inductive"
  dependency (.inductInfo ind)
  modify fun s => { s with constructorTypes := s.constructorTypes.insert name }
  for ctor in ind.ctors do
    let .ctorInfo ci ← getConstInfo ctor
      | throwError "incomplete_closure:E4c.constructor_description"
    dependency (.ctorInfo ci)
    let inspect : CompileM Unit := fun state =>
      forallTelescope ci.type fun fields _ => do
        let mut current := state
        for i in [:fields.size] do
          let domain ← inferType fields[i]!
          if i ≥ ind.numParams then
            let (domain, next) ← (eraseInput domain).run current
            current := next
            if domain.isAppOf name then
              unless domain.getAppArgs.size == ind.numParams do
                throwError "unclassified_form:E4c.recursive_parameters"
              for (a, b) in domain.getAppArgs.zip (fields.extract 0 ind.numParams) do
                let (expected, next) ← (eraseInput b).run current
                current := next
                unless a.equal expected do
                  throwError "unclassified_form:E4c.recursive_parameters"
            else
              if (domain.find? fun e => e.isConstOf name).isSome then
                throwError "unclassified_form:E4c.nested_recursion"
              let (_, next) ← (compileExpr domain 0 true).run current
              current := next
        return ((), current)
    inspect
  rule "E4c.description_v1"

/-- Finite enrollment. The constructor is private and only its checked output
can enter the persistent extension; public query data never grants insertion. -/
private def compileTemplate (name : Name) (constructors : Array Name) : MetaM CheckedTemplatePlan := do
  let env ← getEnv
  let .defnInfo info ← getConstInfo name | throwError "unclassified_form:E1.definition_kind"
  if info.safety != .safe || info.all.length > 1 || (← isRecursiveDefinition name) then
    throwError "unclassified_form:E1.recursive_definition"
  let some owner := ownerOf env name | throwError "incomplete_closure:E7.owner"
  if name.toString.utf8ByteSize > 1024 then throwError "incomplete_closure:E8.name_bytes"
  let limit := min 524288 (informationTemplate.work.get (← getOptions))
  let action : CompileM (Array Slot × PlanNode × PlanNode) := do
    dependency (.defnInfo info)
    for ast in constructors do checkConstructorType ast
    let erasedType ← eraseInput info.type
    let slots ← checkTelescope erasedType
    let typePlan ← compileExpr erasedType 0 true
    let plan ← compileExpr (← eraseInput info.value) 0 false slots.size
    return (slots, typePlan, plan)
  let ((slots, typePlan, plan), state) ← action.run { remaining := limit }
  let .ok (typeIdentity, typeBytes) ← rawIdentity info.levelParams info.type state.remaining
    | throwError "incomplete_closure:E7.type_identity"
  let .ok (bodyIdentity, bodyBytes) ← rawIdentity info.levelParams info.value (state.remaining - typeBytes)
    | throwError "incomplete_closure:E7.body_identity"
  let inputs ← sourceInputs env state.dependencies
  let policyIdentity := sourceIdentity (inputs.filter fun input => policyPaths.contains input.path)
  let data : TemplatePlanData := {
    compiler := Lean.versionString, toolchain := Lean.versionString,
    policyIdentity, sourceInputs := inputs,
    name, definitionOwner := owner, enrollmentOwner := env.header.mainModule,
    levelParams := info.levelParams, slots, constructorTypes := constructors,
    typeIdentity, bodyIdentity, planIdentity := "", dependencies := state.dependencies,
    plan, typePlan, rules := state.rules,
    chargedWork := limit - state.remaining + typeBytes + bodyBytes, serializedBytes := 0 }
  let available := state.remaining - typeBytes - bodyBytes
  let (_, firstWork) ← match planEncodingWithWork data available with
    | .ok result => pure result
    | .error reason => throwError reason
  -- Two serialization passes are both charged; the counter is fixed-width.
  let data := { data with chargedWork := data.chargedWork + 2 * firstWork }
  let (bytes, secondWork) ← match planEncodingWithWork data (available - firstWork) with
    | .ok result => pure result
    | .error reason => throwError reason
  unless firstWork == secondWork do throwError "incomplete_closure:E8.serialization"
  let frame : TemplatePlanFrame := { key := name.toString.toUTF8, payload := bytes, identity := Sha256.hex bytes }
  if frame.retainedBytes > 65536 then throwError "incomplete_closure:E8.plan_bytes"
  return { data := { data with planIdentity := frame.identity, serializedBytes := bytes.size }, frame }

def diagnosticFields (message : String) : String :=
  match message.splitOn ":" with
  | reason :: rule :: site =>
    "reason=" ++ reason ++ " rule=" ++ rule ++ " site=" ++
      (Json.str (String.intercalate ":" site)).compress
  | _ => "reason=incomplete_closure rule=E8.exception site=" ++ (Json.str message).compress

/-- Nested Meta boundaries may use their own initial heartbeat count. The
outer boundary still settles all elapsed work, including the final subcall. -/
def withCumulativeBudget (action : MetaM α) : MetaM α :=
  withCurrHeartbeats <| withOptions (fun options =>
    let configured := maxHeartbeats.get options
    options.set `maxHeartbeats (if configured == 0 then 100000 else min 100000 configured)) do
    let limit := Core.getMaxHeartbeats (← getOptions)
    -- withOptions changes options/maxRecDepth, not Core's heartbeat field.
    controlAt CoreM fun runInBase => withReader (fun context : Core.Context =>
      { context with maxHeartbeats :=
          if context.maxHeartbeats == 0 then limit else min limit context.maxHeartbeats }) do
      let result ← runInBase action
      Core.checkMaxHeartbeats "template cumulative budget"
      return result

/-- Unsupported enrollment leaves no summary. All budgets are lower-only. -/
def enroll (name : Name) (constructors : Array Name := #[]) : CommandElabM (Except String Unit) := do
  let saved ← getEnv
  let answer ← liftTermElabM <| tryCatchRuntimeEx
    (withCumulativeBudget do
      let checkedPlan ← compileTemplate name constructors
      let current := templateIndexExt.getState (← getEnv)
      match current.lookup name (pure () : Id Unit) with
      | .ok _ => throwError "unclassified_form:E7.duplicate_enrollment"
      | .error _ => pure ()
      if let some error := current.error then throwError error
      if current.bytes + checkedPlan.frame.retainedBytes > 8388608 then
        throwError "incomplete_closure:E8.import_bytes"
      modifyEnv fun env => templateIndexExt.addEntry env checkedPlan
      pure (.ok ()))
    (fun error => do
      let message ← error.toMessageData.toString
      pure (.error (if message.startsWith "unclassified_form:" ||
          message.startsWith "forbidden_dependency:" || message.startsWith "incomplete_closure:"
        then message else "incomplete_closure:E8.elaboration:" ++ message)))
  if answer matches .error _ then setEnv saved
  return answer

/-- Numeric literals are indices only at explicit Nat telescope positions. -/
def indexPositions (type : Expr) : Array Bool := Id.run do
  let mut current := type
  let mut positions := #[]
  while let .forallE _ domain body _ := current do
    positions := positions.push (domain.isConstOf ``Nat)
    current := body
  return positions

/-- Supplied arguments and every expanded executable dependency use exactly
 the enrollment compiler. Proof propositions are checked before data identity
 checks, projection reduction and definition substitution. There is no carrier-decoding shortcut. -/
def checkArguments (theoremName : Name) (arguments : Array Expr) (available : Nat)
    (constructors : Array Name := #[]) (indices : Array Bool := #[]) : MetaM (Array Name × Nat) := do
  let limit := min (min 524288 available)
    (RegistrationGates.provenanceExpressionLimit.get (← getOptions))
  if limit == 0 then throwError "incomplete_closure:E8.argument_work"
  let identity ← RegistrationGates.argumentIdentityState theoremName limit
  let action : CompileM Unit := do
    for ast in constructors do checkConstructorType ast
    for i in [:arguments.size] do
      discard <| compileExpr (← eraseInput arguments[i]!) 0 (indices[i]?.getD false)
  let (_, state) ← action.run { remaining := identity.exprFuel, identityState := some identity }
  return (state.dependencies.map (·.name), limit - state.remaining)

/-- Extraction helper types satisfy the same E2/E6 judgment. This examines a
helper's type, not the selected template body, and returns its actual work debit. -/
def checkExtractionType (type : Expr) (available : Nat)
    (constructors : Array Name := #[]) : MetaM (Array DependencyIdentity × Nat) := do
  let limit := min 524288 available
  let action : CompileM Unit := do
    for ast in constructors do checkConstructorType ast
    discard <| compileExpr (← eraseInput type) 0 true
  let (_, state) ← action.run { remaining := limit }
  return (state.dependencies, limit - state.remaining)

end LeanInformationAudit.TemplateAudit

namespace LeanInformationAudit.RegistrationGates
open Lean

/-- Current declared argument entry, shared with enrollment's finite grammar. -/
def templateArgumentsCurrent (theoremName : Name) (arguments : Array Expr)
    (availableWork : Nat) (constructors : Array Name := #[]) (indices : Array Bool := #[]) :
    CoreM (Except String (Array Name × Nat)) :=
  Meta.MetaM.run' <| tryCatchRuntimeEx
    (TemplateAudit.withCumulativeBudget <| .ok <$> TemplateAudit.checkArguments
      theoremName arguments availableWork constructors indices)
    (fun error => do
      let message ← error.toMessageData.toString
      return .error (if message.startsWith "unclassified_form:" ||
          message.startsWith "forbidden_dependency:" || message.startsWith "incomplete_closure:"
        then message else "incomplete_closure:E8.argument_elaboration:" ++ message))

end LeanInformationAudit.RegistrationGates

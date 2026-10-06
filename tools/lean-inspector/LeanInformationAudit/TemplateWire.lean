import LeanInformationAudit.TemplateData
import LeanInformationAudit.Sha256

namespace LeanInformationAudit.TemplateAudit
open Lean

private structure WireState where
  bytes : ByteArray := {}
  remaining : Nat := 524288
  tokens : Option (Std.HashMap String Nat) := none
  expressions : Option (Std.HashMap ExprStructEq Nat) := none
  names : Option (Std.HashMap Name (Nat × Nat)) := none

private abbrev WireM := StateT WireState (Except String)

private def wireCharge (amount : Nat) : WireM Unit := do
  unless amount ≤ (← get).remaining do throw "incomplete_closure:E8.serialization"
  modify fun s => { s with remaining := s.remaining - amount }

private def emitLiteral (text : String) : WireM Unit := do
  let bytes := text.toUTF8
  let lengthPrefix := (toString bytes.size ++ ":").toUTF8
  let size := lengthPrefix.size + bytes.size
  wireCharge size
  modify fun s => { s with bytes := s.bytes ++ lengthPrefix ++ bytes }

private def emit (text : String) : WireM Unit := do
  let some tokens := (← get).tokens | emitLiteral text
  -- Plans and source DAGs intern tokens. Charge every token's full input even on a hit;
  -- compression must not conceal logical serialization work.
  wireCharge (text.utf8ByteSize + 1)
  if let some index := tokens[text]? then
    let reference := ("@" ++ toString index ++ ":").toUTF8
    wireCharge reference.size
    modify fun s => { s with bytes := s.bytes ++ reference }
  else
    emitLiteral text
    modify fun s => { s with tokens := some (tokens.insert text tokens.size) }

private def wireName (name : Name) (depth : Nat := 0) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.name_depth"
  if let some names := (← get).names then
    if let some (index, height) := names[name]? then
      if depth + height > 256 then throw "incomplete_closure:E8.name_depth"
      emit "name-ref"
      emit (toString index)
      return
    emit "name-node"
    modify fun state => { state with names := some (names.insert name (names.size, name.getNumParts)) }
  match name with
  | .anonymous => emit "anonymous"
  | .str parent value => emit "str"; wireName parent (depth + 1); emit value
  | .num parent value => emit "num"; wireName parent (depth + 1); emit (toString value)

private def wireLevel (params : List Name) (level : Level) (depth : Nat := 0) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.level_depth"
  match level with
  | .zero => emit "zero"
  | .succ value => emit "succ"; wireLevel params value (depth + 1)
  | .max a b => emit "max"; wireLevel params a (depth + 1); wireLevel params b (depth + 1)
  | .imax a b => emit "imax"; wireLevel params a (depth + 1); wireLevel params b (depth + 1)
  | .param name =>
    if params.contains name then emit "parameter"; emit (toString (params.idxOf name))
    else emit "rigid"; wireName name
  | .mvar _ => throw "incomplete_closure:E7.level_metavariable"

private def wireSubstring (s : Substring.Raw) : WireM Unit := do
  emit s.str; emit (toString s.startPos.byteIdx); emit (toString s.stopPos.byteIdx)

private def wireSource : SourceInfo → WireM Unit
  | .none => emit "none"
  | .synthetic p q canonical => do
    emit "synthetic"; emit (toString p.byteIdx); emit (toString q.byteIdx); emit (toString canonical)
  | .original leading p trailing q => do
    emit "original"; wireSubstring leading; emit (toString p.byteIdx)
    wireSubstring trailing; emit (toString q.byteIdx)

private partial def wireSyntax (depth : Nat) (stx : Syntax) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.syntax_depth"
  match stx with
  | .missing => emit "missing"
  | .atom info value => emit "atom"; wireSource info; emit value
  | .node info kind children =>
    emit "node"; wireSource info; wireName kind; emit (toString children.size)
    for child in children do wireSyntax (depth + 1) child
  | .ident info raw name pre =>
    emit "ident"; wireSource info; wireSubstring raw; wireName name; emit (toString pre.length)
    for item in pre do
      match item with
      | .namespace name => emit "namespace"; wireName name
      | .decl name fields =>
        emit "decl"; wireName name; emit (toString fields.length)
        for field in fields do emit field

private def wireData (depth : Nat) : DataValue → WireM Unit
  | .ofString value => do emit "string"; emit value
  | .ofBool value => do emit "bool"; emit (toString value)
  | .ofName value => do emit "name"; wireName value
  | .ofNat value => do emit "nat"; emit (toString value)
  | .ofInt value => do emit "int"; emit (toString value)
  | .ofSyntax value => do emit "syntax"; wireSyntax depth value

private partial def wireExpr (params : List Name) (depth : Nat) (e : Expr)
    (key : Expr := e) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.expression_depth"
  if let some expressions := (← get).expressions then
    if let some index := expressions[ExprStructEq.mk key]? then
      emit "expr-ref"
      emit (toString index)
      return
    emit "expr-node"
    modify fun state => { state with expressions := some (expressions.insert ⟨key⟩ expressions.size) }

  let child := fun x k => wireExpr params (depth + 1) x k
  match e with
  | .bvar index => emit "bvar"; emit (toString index)
  | .fvar _ | .mvar _ => throw "incomplete_closure:E7.open_expression"
  | .sort level => emit "sort"; wireLevel params level
  | .const name levels =>
    emit "const"; wireName name; emit (toString levels.length)
    for level in levels do wireLevel params level
  | .app f a => emit "app"; child f key.appFn!; child a key.appArg!
  | .lam _ type body bi =>
    emit "lambda"; emit (reprStr bi); child type key.bindingDomain!; child body key.bindingBody!
  | .forallE _ type body bi =>
    emit "forall"; emit (reprStr bi); child type key.bindingDomain!; child body key.bindingBody!
  | .letE _ type value body nd =>
    emit "let"; emit (toString nd)
    child type key.letType!; child value key.letValue!; child body key.letBody!
  | .lit (.natVal n) => emit "natLiteral"; emit (toString n)
  | .lit (.strVal s) => emit "stringLiteral"; emit s
  | .mdata data body =>
    emit "metadata"; emit (toString data.entries.length)
    for (key, value) in data.entries do wireName key; wireData (depth + 1) value
    child body key.mdataExpr!
  | .proj name index body =>
    emit "projection"; wireName name; emit (toString index); child body key.projExpr!

/-- Domain-separated, length-prefixed raw Expr/Level identity. Binder names are
anonymous; instances, lets and metadata retain their complete structural bytes. -/
def erasedSyntaxIdentity (params : List Name) (e : Expr) (fuel : Nat := 524288) : Except String (String × Nat) := do
  let action : WireM Unit := do emit "DTR-proof-erased-expr-v2"; wireExpr params 0 e
  let (_, state) ← action.run { remaining := min fuel 524288 }
  return (Sha256.hex state.bytes, state.bytes.size)

/-- Occurrence statements retain their established identity dialect. This is a
statement address, not a descriptor/realization comparison or body digest. -/
def rawStatementIdentity (params : List Name) (e : Expr) (fuel : Nat := 524288) :
    Except String (String × Nat) := do
  let action : WireM Unit := do emit "DTR-raw-expr-v1"; wireExpr params 0 e
  let (_, state) ← action.run { remaining := min fuel 524288 }
  return (Sha256.hex state.bytes, state.bytes.size)

-- Expr.eqv ignores BinderInfo; even Expr.equal compares metadata Syntax modulo
-- source information. Build structural keys with anonymous binder names and
-- exact metadata wire bytes. The emitted expression itself is never rewritten.
-- The canonical DAG walk retains subtree heights and checks every occurrence,
-- including repeated subtrees that the subsequent wire pass will reference.
private structure SourceKeyState where
  remaining : Nat
  nodes : Std.HashMap USize (Expr × Nat) := {}
  maxDepth : Nat := 0

private partial def sourceKey (e : Expr) (depth : Nat := 0) :
    StateT SourceKeyState (Except String) Expr := do
  if depth > 256 then throw "incomplete_closure:E8.expression_depth"
  modify fun state => { state with maxDepth := max state.maxDepth depth }
  let remaining := (← get).remaining
  if remaining == 0 then throw "incomplete_closure:E8.source_identity_work"
  modify fun state => { state with remaining := remaining - 1 }
  -- Pointer equality is exact syntax equality while the input DAG is live.
  -- A reused subtree still checks its deepest occurrence against the same limit.
  let address := unsafe ptrAddrUnsafe e
  if let some (key, height) := (← get).nodes[address]? then
    if depth + height > 256 then throw "incomplete_closure:E8.expression_depth"
    modify fun state => { state with maxDepth := max state.maxDepth (depth + height) }
    return key
  let enclosingDepth := (← get).maxDepth
  modify fun state => { state with maxDepth := depth }
  let child := fun x => sourceKey x (depth + 1)
  let key ← match e with
    | .app f a => pure <| .app (← child f) (← child a)
    | .lam _ t b bi => pure <| .lam .anonymous (← child t) (← child b) bi
    | .forallE _ t b bi => pure <| .forallE .anonymous (← child t) (← child b) bi
    | .letE _ t v b nd => pure <| .letE .anonymous (← child t) (← child v) (← child b) nd
    | .mdata data b => do
      let action : WireM Unit := do
        emit (toString data.entries.length)
        for (name, value) in data.entries do wireName name; wireData (depth + 1) value
      let (_, state) ← action.run { remaining := (← get).remaining }
      modify fun current => { current with remaining := state.remaining }
      pure <| .mdata ⟨[(.anonymous, .ofString (String.fromUTF8! state.bytes))]⟩ (← child b)
    | .proj n i b => pure <| .proj n i (← child b)
    | _ => pure e
  let height := (← get).maxDepth - depth
  modify fun state => { state with
    nodes := state.nodes.insert address (key, height)
    maxDepth := max enclosingDepth state.maxDepth }
  return key

/-- Canonical shared raw Expr references for source-bound contracts. This does
not change the mathematical statement_id or the existing raw identity dialect.
The key pass checks stored subtree heights at every repeated occurrence.
Raw proof subterms, levels, metadata, lets and BinderInfo remain in the encoding. -/
def compactRawEncoding (params : List Name) (e : Expr) (fuel : Nat := 524288) :
    Except String (ByteArray × Nat) := do
  let limit := min 524288 fuel
  let (key, keys) ← sourceKey e |>.run { remaining := limit }
  let action : WireM Unit := do
    emit "DTR-source-expr-dag-v2"
    wireExpr params 0 e key
  let (_, state) ← action.run {
    remaining := keys.remaining, tokens := some {}, expressions := some {}, names := some {} }
  if state.bytes.size > 65536 then throw "incomplete_closure:E8.source_identity_bytes"
  return (state.bytes, limit - state.remaining)

def compactRawIdentity (params : List Name) (e : Expr) (fuel : Nat := 524288) :
    Except String (String × Nat) :=
  (compactRawEncoding params e fuel).map fun (bytes, work) => (Sha256.hex bytes, work)

/-- Complete binding evidence uses canonical token and name references.
Dependency arrays are separate length-delimited inputs, not annotations
outside the evidence identity. The evidence reference itself is not encoded. -/
def bindingIdentity (statementIdentity : String) (certificate : TemplateBindingCertificate)
    (fuel : Nat) : Except String (String × Nat) := do
  let action : WireM Unit := do
    emit "DTR-binding-evidence-v3"
    for name in #[certificate.key.root, certificate.key.registrationModule,
        certificate.key.theoremName, certificate.key.objectArena, certificate.key.catalog] do
      wireName name
    emit statementIdentity
    emit certificate.planIdentity
    emit certificate.descriptorIdentity
    emit certificate.actualIdentity
    emit certificate.escape.bridgeKind
    if let some source := certificate.sourceBinding then
      emit "source-binding"
      emit source.compress
    match certificate.escape.fromObject with
    | none => emit "missing-from"
    | some origin =>
      wireName origin.name; emit origin.typeIdentity; emit origin.objectIdentity
    match certificate.escape.continuation with
    | none => emit "missing-continuation"
    | some residual =>
      emit residual.kind
      wireName (residual.declarationName.getD .anonymous)
      emit (residual.statementIdentity.getD "")
      wireName (residual.chainName.getD .anonymous)
    for inputs in #[certificate.argumentInputs, certificate.extractionInputs] do
      emit (toString inputs.size)
      for input in inputs do
        wireName input.name; wireName input.owner
        emit input.typeIdentity; emit input.bodyIdentity
  let limit := min fuel 524288
  let (_, state) ← action.run { remaining := limit, tokens := some {}, names := some {} }
  return (Sha256.hex state.bytes, limit - state.remaining)

/-- Share canonical expression subgraphs in a plan while separately checking
all raw depths and metadata before a wire reference can replace a subtree. -/
private def canonicalExpr (params : List Name) (depth : Nat) (e : Expr) : WireM Unit := do
  let available := (← get).remaining
  let (key, keys) ← sourceKey e depth |>.run { remaining := available }
  wireCharge (available - keys.remaining)
  wireExpr params depth e key

private partial def wirePlan (params : List Name) (depth : Nat) (plan : PlanNode) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.plan_depth"
  let child := wirePlan params (depth + 1)
  let raw := canonicalExpr params (depth + 1)
  match plan with
  | .atom e => emit "body"; raw e
  | .supplied _ => throw "incomplete_closure:E7.supplied_in_static_plan"
  | .expanded e body => emit "expanded"; raw e; child body
  | .proofLeaf type => emit "proof-leaf"; raw type
  | .typeNode checked => emit "type-node"; child checked
  | .audit input body => emit "audit-input"; child input; child body
  | .app f a => emit "application"; child f; child a
  | .lam t b bi => emit "lambda"; emit (reprStr bi); child t; child b
  | .forallE t b bi => emit "forall"; emit (reprStr bi); child t; child b
  | .letE t v b nd => emit "let"; emit (toString nd); child t; child v; child b
  | .mdata m b => emit "metadata"; raw (.mdata m (.bvar 0)); child b
  | .proj n i b => emit "projection"; wireName n; emit (toString i); child b

/-- The canonical wire includes every retained plan node and proof proposition/erased expansion,
all slots, identities, the private frame version tuple. The hash and byte count are
outputs of this encoding and are not recursively encoded inside themselves. -/
def planEncodingWithWork (plan : TemplatePlanData) (fuel : Nat := 524288) :
    Except String (ByteArray × Nat) := do
  let action : WireM Unit := do
    emit "DTR-checked-plan-v8"
    for version in #[plan.schemaVersion, plan.grammarVersion, plan.constructorRecursionVersion,
        plan.compatibilityVersion] do emit (toString version)
    emit plan.compiler; emit plan.toolchain
    wireName plan.name; wireName plan.definitionOwner; wireName plan.enrollmentOwner
    emit (toString plan.levelParams.length)
    emit plan.typeIdentity; emit plan.bodyIdentity
    emit (toString plan.slots.size)
    for slot in plan.slots do
      emit (reprStr slot.kind); emit (reprStr slot.binderInfo)
      canonicalExpr plan.levelParams 0 slot.type
    emit (toString plan.dependencies.size)
    for dep in plan.dependencies do
      wireName dep.name; wireName dep.owner; emit dep.typeIdentity; emit dep.bodyIdentity
    emit (toString plan.sourceBound)
    emit (toString plan.constructorTypes.size)
    for ast in plan.constructorTypes do wireName ast
    emit (toString plan.rules.size)
    for rule in plan.rules do emit rule
    -- The fixed-width work field is outside the token table so its changing
    -- digits cannot affect references, serialized size or either pass's work.
    emitLiteral (String.ofList (List.replicate (6 - (toString plan.chargedWork).length) '0') ++ toString plan.chargedWork)
    wirePlan plan.levelParams 0 plan.typePlan
    wirePlan plan.levelParams 0 plan.plan
  let limit := min fuel 524288
  let (_, state) ← action.run { remaining := limit, tokens := some {}, expressions := some {}, names := some {} }
  if state.bytes.size > 65536 then throw s!"incomplete_closure:E8.plan_bytes:{state.bytes.size}"
  return (state.bytes, limit - state.remaining)
def planEncoding (plan : TemplatePlanData) (fuel : Nat := 524288) : Except String ByteArray :=
  (planEncodingWithWork plan fuel).map Prod.fst


end LeanInformationAudit.TemplateAudit

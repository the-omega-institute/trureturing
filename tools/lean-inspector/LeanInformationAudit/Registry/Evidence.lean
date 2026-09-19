import LeanInformationAudit.Registry.Entries

namespace LeanInformationAudit.TemplateAudit
open Lean Meta

private abbrev EraseM := StateT Nat MetaM

private partial def erase (e : Expr) (depth : Nat) : EraseM Expr := do
  Core.checkMaxHeartbeats "template proof erasure"
  if depth > 256 then throwError "incomplete_closure:E8.erasure_depth"
  let remaining ← get
  if remaining == 0 then throwError "incomplete_closure:E8.erasure_work"
  set (remaining - 1)
  -- Inference classifies the proposition; no visitor descends into a proof.
  if ← isProof e then return proofPlaceholder (← erase (← inferType e) (depth + 1))
  let child := fun e => erase e (depth + 1)
  match e with
  | .app f a => return .app (← child f) (← child a)
  | .lam n t b bi | .forallE n t b bi =>
    let type ← child t
    let body ← fun state => withLocalDecl n bi t fun x => do
      let (body, state) ← (child (b.instantiate1 x)).run state
      return (body.abstract #[x], state)
    return if e.isLambda then .lam n type body bi else .forallE n type body bi
  | .letE n t v b nd =>
    let type ← child t
    let value ← child v
    let body ← fun state => withLetDecl n t v fun x => do
      let (body, state) ← (child (b.instantiate1 x)).run state
      return (body.abstract #[x], state)
    return .letE n type value body nd
  | .mdata m b => return .mdata m (← child b)
  | .proj n i b => return .proj n i (← child b)
  | .mvar _ => throwError "incomplete_closure:E7.metavariable"
  | .bvar _ => throwError "incomplete_closure:E7.open_expression"
  | _ => return e

/-- Preserve all data syntax and replace each proof by its proposition. Typing
uses the original binder domains; the result retains no proof implementation.
The caller charges this walk before any transformation or serialization. -/
def eraseProofs (e : Expr) (fuel : Nat := 524288) : MetaM (Expr × Nat) := do
  let limit := min fuel 524288
  let (result, remaining) ← (erase e 0).run limit
  return (result, limit - remaining)

register_option informationTemplate.work : Nat := {
  defValue := 524288
  descr := "Lower-only DTR expression, substitution and byte-work quota" }

private structure WireState where
  bytes : ByteArray := {}
  remaining : Nat := 524288
  tokens : Option (Std.HashMap String Nat) := none

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
  -- Interning is plan-only. Charge every token's full input even on a hit;
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

private partial def wireExpr (params : List Name) (depth : Nat) (e : Expr) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.expression_depth"
  let child := fun x => wireExpr params (depth + 1) x
  match e with
  | .bvar index => emit "bvar"; emit (toString index)
  | .fvar _ | .mvar _ => throw "incomplete_closure:E7.open_expression"
  | .sort level => emit "sort"; wireLevel params level
  | .const name levels =>
    emit "const"; wireName name; emit (toString levels.length)
    for level in levels do wireLevel params level
  | .app f a => emit "app"; child f; child a
  | .lam _ type body bi => emit "lambda"; emit (reprStr bi); child type; child body
  | .forallE _ type body bi => emit "forall"; emit (reprStr bi); child type; child body
  | .letE _ type value body nd =>
    emit "let"; emit (toString nd); child type; child value; child body
  | .lit (.natVal n) => emit "natLiteral"; emit (toString n)
  | .lit (.strVal s) => emit "stringLiteral"; emit s
  | .mdata data body =>
    emit "metadata"; emit (toString data.entries.length)
    for (key, value) in data.entries do wireName key; wireData (depth + 1) value
    child body
  | .proj name index body => emit "projection"; wireName name; emit (toString index); child body

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

/-- The forward bridge is recognized by its type name, without importing content
into the finite seal closure. Both bridges retain the exact statement check. -/
def escapeForwardBridge : Name :=
  `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapePrimitiveRealization

def bridgeKind (event : TemplateOccurrenceEvent) : MetaM String := do
  let type := (← getConstInfo event.realizationName).type
  return if type.isAppOfArity escapeForwardBridge 3 then "forward" else "legacy"

private def escapeIdentity (params : List Name) (value : Expr) : MetaM String := do
  let .ok (identity, _) := rawStatementIdentity params value
    | throwError "incomplete_closure:dtr.escape_identity"
  return identity

/-- This check consumes only names, expression occurrence, and kernel types.
No state, chain, certificate body, or residual count is evaluated. -/
def checkEscapeRecord (event : TemplateOccurrenceEvent) (input : EscapeRecordInput) :
    MetaM EscapeRecordEvidence := do
  let mut arena := event.arena
  if (← inferType arena).isAppOf
      `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena then
    arena ← mkAppM `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.toArena #[arena]
  let fromObject ← input.fromObject.mapM fun origin => do
    unless (event.statement.find? (·.equal origin)).isSome do
      throwError "unclassified_form:dtr.escape_from_absent"
    let some name := origin.getAppFn.constName?
      | throwError "unclassified_form:dtr.escape_from_identity"
    if origin.hasFVar || origin.hasMVar || origin.hasLooseBVars then
      throwError "unclassified_form:dtr.escape_from_identity"
    let type ← inferType origin
    let state ← mkAppM `D5.S3.ConceptDynamics.InformationEscape.Arena.State #[arena]
    let represented := if ← isType origin then origin else type
    unless ← isDefEq represented state do
      throwError "unclassified_form:dtr.escape_from_state"
    let typeIdentity ← escapeIdentity event.levelParams type
    let objectIdentity ← escapeIdentity event.levelParams origin
    return (⟨name, typeIdentity, objectIdentity⟩ : EscapeFromIdentity)
  let continuation ← if input.openContinuation then
      if input.continuation.isSome then throwError "unclassified_form:dtr.escape_continues_kind"
      pure <| some { kind := "open" : EscapeContinuationIdentity }
    else input.continuation.mapM fun value => do
      let .const declarationName levels := value
        | throwError "unclassified_form:dtr.escape_continues_named_certificate"
      let info ← getConstInfo declarationName
      unless levels.length == info.levelParams.length do
        throwError "unclassified_form:dtr.escape_continues_named_certificate"
      let type ← inferType value
      let kind ← if type.isAppOfArity
          `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapeResidualWitness 2 then
          pure "witness"
        else if type.isAppOfArity
          `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapeResidualEmpty 2 then
          pure "empty"
        else throwError "unclassified_form:dtr.escape_continues_kind"
      let args := type.getAppArgs
      let chain := args[1]!
      let .const chainName _ := chain
        | throwError "unclassified_form:dtr.escape_continues_named_chain"
      let chainType ← inferType chain
      unless chainType.isAppOfArity `D5.S3.ConceptDynamics.InformationEscape.LayerChain 1 &&
          (← isDefEq args[0]! arena) && (← isDefEq chainType.appArg! arena) do
        throwError "unclassified_form:dtr.escape_continues_arena"
      if kind == "witness" then
        let membership ← mkAppM
          `D5.S3.ConceptDynamics.InformationEscape.EscapeRecord.EscapeResidualWitness.unresolved #[value]
        unless ← isProof membership do throwError "unclassified_form:dtr.escape_continues_membership"
        unless (← inferType membership).isAppOf ``Membership.mem do
          throwError "unclassified_form:dtr.escape_continues_membership"
      else unless ← isProof value do throwError "unclassified_form:dtr.escape_continues_kind"
      let statementIdentity ← escapeIdentity info.levelParams info.type
      return (⟨kind, some declarationName, some statementIdentity, some chainName⟩ :
        EscapeContinuationIdentity)
  return { fromObject, continuation, bridgeKind := (← bridgeKind event) }

/-- Typed identity stops at each proof and serializes its proposition instead.
The pure wire encoder is exposed separately for synthetic encoding tests. -/
def rawIdentity (params : List Name) (e : Expr) (fuel : Nat := 524288) :
    MetaM (Except String (String × Nat)) := do
  let (erased, work) ← eraseProofs e fuel
  return (erasedSyntaxIdentity params erased (fuel - work)).map fun (identity, bytes) =>
    (identity, work + bytes)

/-- Complete binding evidence uses the unshared raw-identity wire format.
Dependency arrays are separate length-delimited inputs, not annotations
outside the evidence identity. The evidence reference itself is not encoded. -/
def bindingIdentity (statementIdentity : String) (certificate : TemplateBindingCertificate)
    (fuel : Nat) : Except String (String × Nat) := do
  let action : WireM Unit := do
    emit "DTR-binding-evidence-v3"
    for name in #[certificate.key.root, certificate.key.registrationModule,
        certificate.key.theoremName, certificate.key.objectArena, certificate.key.catalog] do
      wireName name
    emit certificate.key.mode.wireName
    emit statementIdentity
    emit certificate.planIdentity
    emit certificate.descriptorIdentity
    emit certificate.actualIdentity
    emit certificate.escape.bridgeKind
    emit (certificate.escape.family.map (·.identity) |>.getD "fixed")
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
  let (_, state) ← action.run { remaining := min fuel 524288 }
  return (Sha256.hex state.bytes, state.bytes.size)

private partial def wirePlan (params : List Name) (depth : Nat) (plan : PlanNode) : WireM Unit := do
  if depth > 256 then throw "incomplete_closure:E8.plan_depth"
  let child := wirePlan params (depth + 1)
  let raw := wireExpr params (depth + 1)
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
all slots, identities, policy and source references. The hash and byte count are
outputs of this encoding and are not recursively encoded inside themselves. -/
def planEncodingWithWork (plan : TemplatePlanData) (fuel : Nat := 524288) :
    Except String (ByteArray × Nat) := do
  let action : WireM Unit := do
    emit "DTR-checked-plan-v6"
    for version in #[plan.schemaVersion, plan.grammarVersion, plan.constructorRecursionVersion,
        plan.compatibilityVersion] do emit (toString version)
    emit plan.mode.wireName
    emit plan.compiler; emit plan.toolchain; emit plan.policyIdentity
    wireName plan.name; wireName plan.definitionOwner; wireName plan.enrollmentOwner
    emit (toString plan.levelParams.length)
    emit plan.typeIdentity; emit plan.bodyIdentity
    emit (toString plan.slots.size)
    for slot in plan.slots do
      emit (reprStr slot.kind); emit (reprStr slot.binderInfo)
      wireExpr plan.levelParams 0 slot.type
    emit (toString plan.dependencies.size)
    for dep in plan.dependencies do
      wireName dep.name; wireName dep.owner; emit dep.typeIdentity; emit dep.bodyIdentity
    emit (toString plan.constructorTypes.size)
    for ast in plan.constructorTypes do wireName ast
    emit (toString plan.sourceInputs.size)
    for input in plan.sourceInputs do emit input.path; emit input.sha256
    emit (toString plan.rules.size)
    for rule in plan.rules do emit rule
    -- The fixed-width work field is outside the token table so its changing
    -- digits cannot affect references, serialized size or either pass's work.
    emitLiteral (String.ofList (List.replicate (6 - (toString plan.chargedWork).length) '0') ++ toString plan.chargedWork)
    wirePlan plan.levelParams 0 plan.typePlan
    wirePlan plan.levelParams 0 plan.plan
  let limit := min fuel 524288
  let (_, state) ← action.run { remaining := limit, tokens := some {} }
  if state.bytes.size > 65536 then throw s!"incomplete_closure:E8.plan_bytes:{state.bytes.size}"
  return (state.bytes, limit - state.remaining)

def planEncoding (plan : TemplatePlanData) (fuel : Nat := 524288) : Except String ByteArray :=
  (planEncodingWithWork plan fuel).map Prod.fst

def sourcePath (name : Name) : String :=
  (if name.toString.startsWith "LeanInformationAudit." then "tools/lean-inspector/" else "") ++
    name.toString.replace "." "/" ++ ".lean"

-- Judge implementation bytes do not identify binding semantics; the manual
-- report_semantic_version does. Retain configuration and toolchain inputs.
def policyPaths : Array String := #[
  "lean-report-inputs.json", "lean-toolchain", "lake-manifest.json"]

private abbrev HashWorker := IO.Process.Child {
  stdin := .piped, stdout := .piped, stderr := .null }

private initialize hashWorker : Std.Mutex (Option HashWorker) ← Std.Mutex.new none

/-- Reuse only the fixed worker process, never a file digest. Requests carry the
caller's current directory because isolated source fixtures may change it. The
mutex keeps each request/response together; any failure retires the stream. -/
private def fileInputBatch (paths : Array String) : IO (Array String × Option Nat) := do
  if paths.isEmpty then return (#[], none)
  let request := Json.arr #[toJson (← IO.currentDir).toString, toJson paths]
  hashWorker.atomically do
    try
      let child ← match ← get with
        | some child => pure child
        | none => do
          let child ← IO.Process.spawn {
            cmd := "python3", stdin := .piped, stdout := .piped, stderr := .null,
            args := #["-I", "-c",
              "import hashlib,json,pathlib,sys\n" ++
              "def unique(pairs):\n" ++
              " result={}\n" ++
              " for key,value in pairs:\n" ++
              "  if key in result: raise ValueError('duplicate field')\n" ++
              "  result[key]=value\n" ++
              " return result\n" ++
              "for line in sys.stdin.buffer:\n" ++
              " p=None\n" ++
              " try:\n" ++
              "  root,paths=json.loads(line)\n" ++
              "  hashes=[]; version=None\n" ++
              "  for p in paths:\n" ++
              "   data=(pathlib.Path(root)/p).read_bytes()\n" ++
              "   hashes.append(hashlib.sha256(data).hexdigest())\n" ++
              "   if p=='lean-report-inputs.json':\n" ++
              "    version=json.loads(data.decode('utf-8'),object_pairs_hook=unique)['report_semantic_version']\n" ++
              "    if type(version) is not int or version<=0: raise ValueError('version')\n" ++
              "  result=[hashes,version]\n" ++
              " except Exception:\n" ++
              "  result='DTR-ManifestVersion' if p=='lean-report-inputs.json' else None\n" ++
              " print(json.dumps(result,separators=(',',':')),flush=True)\n"] }
          set (some child)
          pure child
      child.stdin.putStr (request.compress ++ "\n")
      child.stdin.flush
      let response ← IO.ofExcept <| Json.parse (← child.stdout.getLine)
      if response.getStr? == .ok "DTR-ManifestVersion" then
        throw <| IO.userError "DTR-ManifestVersion: missing or malformed report_semantic_version"
      let (hashes, version) : Array String × Option Nat ← IO.ofExcept <| fromJson? response
      unless hashes.size == paths.size && hashes.all (fun hash => hash.length == 64 &&
          hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))) do
        throw <| IO.userError "incomplete_closure:E7.native_hash"
      return (hashes, version)
    catch error =>
      let child : Option HashWorker ← get
      set (none : Option HashWorker)
      if let some child := child then
        try child.kill catch _ => pure ()
        try discard <| child.wait catch _ => pure ()
      if error.toString.contains "DTR-ManifestVersion" then throw error
      throw <| IO.userError "incomplete_closure:E7.native_hash"

private def fileHashes (paths : Array String) : IO (Array String) := do
  return (← fileInputBatch paths).1

/-- The version and manifest digest come from the same captured policy bytes. -/
def readVersionedSourceInputs (paths : Array String) : CoreM (Array SourceInput × Nat) := do
  let (hashes, version) ← fileInputBatch paths
  let some version := version
    | throwError "DTR-ManifestVersion: missing report_semantic_version policy input"
  return ((paths.zip hashes).map (fun (path, sha256) => { path, sha256 }), version)

/-- Hash every supplied current file in order, including repeated paths. The
fixed native worker avoids interpreting SHA-256 separately for every byte. -/
def readSourceInputs (paths : Array String) : CoreM (Array SourceInput) := do
  let hashes ← fileHashes paths
  return (paths.zip hashes).map fun (path, sha256) => { path, sha256 }

def readSourceInput (path : String) : CoreM SourceInput := do
  let hashes ← fileHashes #[path]
  return { path, sha256 := hashes[0]! }

/-- Preserve already captured bytes across native validation. Hashing the live
paths again could bind a later replacement to the earlier checked native image. -/
private def capturedHashes (inputs : Array ByteArray) : IO (Array String) :=
  IO.FS.withTempDir fun directory => do
    let paths ← inputs.mapIdxM fun index bytes => do
      let path := directory / s!"input{index}"
      IO.FS.writeBinFile path bytes
      pure path.toString
    fileHashes paths

namespace NativeCoherence

private structure Snapshot where
  inputs : Array SourceInput
  data : ModuleData


private def repositoryModule (name : Name) : Bool :=
  name.toString.startsWith "D5." || name.toString.startsWith "LeanInformationAudit." ||
    name == `Trureturing

private def parseHash (text : String) : Except String UInt64 := do
  unless text.utf8ByteSize == 16 do throw "incomplete_closure:E7.native_trace_hash"
  text.toUTF8.foldlM (init := 0) fun result byte => do
    let digit ← if 48 ≤ byte && byte ≤ 57 then pure (byte - 48) else
      if 97 ≤ byte && byte ≤ 102 then pure (byte - 87)
      else throw "incomplete_closure:E7.native_trace_hash"
    return result * 16 + digit.toUInt64

private def binaryHash (bytes : ByteArray) : UInt64 := mixHash 1723 (hash bytes)
private def textHash (text : String) : UInt64 := mixHash 1723 (hash text.crlfToLf)

private def field (json : Json) (key : String) : CoreM Json :=
  ofExcept <| json.getObjVal? key

private partial def traceHash (value : Json) (depth : Nat := 0) : Except String UInt64 := do
  if depth > 256 then throw "incomplete_closure:E7.native_trace_depth"
  if let .str text := value then return ← parseHash text
  let inputs ← value.getArr?
  inputs.foldlM (init := 1723) fun result input => do
    let pair ← input.getArr?
    unless pair.size == 2 do throw "incomplete_closure:E7.native_trace_pair"
    return mixHash result (← traceHash pair[1]! (depth + 1))

private def child (value : Json) (caption : String) : CoreM Json := do
  let inputs ← ofExcept <| value.getArr?
  let matching := inputs.filter fun input =>
    (((input.getArr?).toOption.bind (·[0]?)).bind (·.getStr?.toOption)) == some caption
  unless matching.size == 1 do throwError "incomplete_closure:E7.native_trace_input:{caption}"
  let pair ← ofExcept <| matching[0]!.getArr?
  unless pair.size == 2 do throwError "incomplete_closure:E7.native_trace_pair"
  return pair[1]!

private structure ExportHash where
  arts : UInt64
  metaArts : UInt64
  allArts : UInt64
  publicTransitive : UInt64
  metaTransitive : UInt64
  allTransitive : UInt64
  transitive : UInt64

private initialize regionIndex : EnvExtension
    (Option (Array CompactedRegion × Std.HashMap String (Option CompactedRegion))) ←
  registerEnvExtension (pure none)

private def loadedRegion (env : Environment) (path : System.FilePath) : CoreM CompactedRegion := do
  let cached := regionIndex.getState (← getEnv)
  let index ← match cached with
    | some (regions, index) =>
      unless (unsafe ptrEq regions env.header.regions) do
        throwError "incomplete_closure:E7.native_regions"
      pure index
    | none =>
      let mut index : Std.HashMap String (Option CompactedRegion) := {}
      for region in env.header.regions do
        let key := region.filePath.toString
        index := index.insert key (if index.contains key then none else some region)
      modifyEnv fun current => regionIndex.setState current (some (env.header.regions, index))
      pure index
  let some (some region) := index[path.toString]?
    | throwError "incomplete_closure:E7.native_mapping:{path}"
  return region

private def moduleFile (env : Environment) (name : Name) : CoreM System.FilePath := do
  let path ← findOLean name
  if repositoryModule name then discard <| loadedRegion env path
  return path

private structure Cache where
  snapshots : Std.HashMap Name Snapshot := {}
  closures : Std.HashMap Name (Array Name) := {}
  exports : Std.HashMap Name ExportHash := {}
  deriving Inhabited

private initialize checked : EnvExtension Cache ← registerEnvExtension (pure {})

private initialize observedInputs : EnvExtension (Array String) ← registerEnvExtension (pure #[])

/-- Read-only observation of the files rechecked by the latest selected validation. -/
def lastInputs (env : Environment) : Array String := observedInputs.getState env

/-- The pinned Lake import modifiers select both transitive and artifact traces. -/
private def importHashes (value : ExportHash) (nonModule : Bool) (imported : Import) :
    String × UInt64 × String × UInt64 :=
  if nonModule then ("legacy", value.transitive, "importAllArts", value.allArts)
  else if imported.importAll then ("all", value.allTransitive, "importAllArts", value.allArts)
  else if imported.isMeta then ("meta", value.metaTransitive, "importArts (meta)", value.metaArts)
  else ("public", value.publicTransitive, "importArts", value.arts)

/-- Reproduce Lake.Module.computeExportInfo's four import hash relations.
Compiler-owned imports have no Lake package trace and are pinned by the Lean
version input. Package traces remain trusted upstream build metadata. -/
private partial def exports (env : Environment) (name : Name)
    (memo : Std.HashMap Name ExportHash) : CoreM (Option ExportHash × Std.HashMap Name ExportHash) := do
  if let some value := memo[name]? then return (some value, memo)
  let artifact ← moduleFile env name
  let tracePath := artifact.withExtension "trace"
  if !(← tracePath.pathExists) then
    -- Lake supplies the compiler prefix to relocated inspector executables.
    -- Inside Lean itself the SDK build directory remains the fallback.
    let sysroot ← match ← IO.getEnv "LEAN_SYSROOT" with
      | some path => pure (System.FilePath.mk path)
      | none => getBuildDir
    let lib ← getLibDir sysroot
    unless (← IO.FS.realPath artifact).toString.startsWith ((← IO.FS.realPath lib).toString ++ "/") do
      throwError "incomplete_closure:E7.native_trace_missing:{name}"
    return (none, memo)
  let trace ← ofExcept <| Json.parse (← IO.FS.readFile tracePath)
  unless trace.getObjValAs? String "schemaVersion" == .ok "2025-09-10" do
    throwError "incomplete_closure:E7.native_trace_version:{name}"
  let output ← field trace "outputs"
  let oleans ← ofExcept <| output.getObjValAs? (Array String) "o"
  let isModule ← ofExcept <| output.getObjValAs? Bool "m"
  unless oleans.size == (if isModule then 3 else 1) do
    throwError "incomplete_closure:E7.native_trace_outputs:{name}"
  let mut parts := oleans
  if isModule then
    parts := parts.push (← ofExcept <| output.getObjValAs? String "rs")
    parts := parts.push (← ofExcept <| output.getObjValAs? String "r")
  let mut allArts := 1723
  for part in parts do
    allArts := mixHash allArts (← ofExcept <| parseHash (part.take 16).toString)
  let arts := mixHash 1723 (← ofExcept <| parseHash (oleans[0]!.take 16).toString)
  let mut metaArts := arts
  if isModule then
    for part in parts.extract 3 5 do
      metaArts := mixHash metaArts (← ofExcept <| parseHash (part.take 16).toString)
  let some index := env.getModuleIdx? name | throwError "incomplete_closure:E7.native_module:{name}"
  let data := env.header.moduleData[index.toNat]!
  let mut memo := memo
  let mut transitive := 1723
  let mut publicTransitive := 1723
  let mut metaTransitive := 1723
  let mut allTransitive := 1723
  for imported in data.imports do
    let (dependency, next) ← exports env imported.module memo
    memo := next
    if let some dependency := dependency then
      transitive := mixHash (mixHash transitive dependency.transitive) dependency.allArts
      metaTransitive := mixHash (mixHash metaTransitive dependency.metaTransitive) dependency.metaArts
      let (_, selected, _, selectedArts) := importHashes dependency false imported
      allTransitive := mixHash (mixHash allTransitive selected) selectedArts
      if imported.isExported then
        let selected := if imported.isMeta then dependency.metaTransitive
          else dependency.publicTransitive
        let selectedArts := if imported.isMeta then dependency.metaArts else dependency.arts
        publicTransitive := mixHash (mixHash publicTransitive selected) selectedArts
  let value : ExportHash := {
    arts := arts
    metaArts := metaArts
    allArts := allArts
    publicTransitive := publicTransitive
    metaTransitive := metaTransitive
    allTransitive := allTransitive
    transitive := transitive }
  return (some value, memo.insert name value)


private def unchanged (inputs : Array SourceInput) : IO Bool := do
  if inputs.isEmpty then return true
  let hashes ← fileHashes (inputs.map (·.path))
  return (inputs.zip hashes).all fun (input, hash) => input.sha256 == hash

/-- Exact runtime layout of the pinned compiler's CompactedRegion. Its private
root is a boxed ModuleData for the engine-loaded olean/IR parts selected below.
This cast never reads a fresh disk image or interprets a content-owned value. -/
private structure RegionLayout where
  filePath : System.FilePath
  size : USize
  isMemoryMapped : Bool
  baseAddr : USize
  bufferOffset : USize
  root : NonScalar

private unsafe def loadedPart (region : CompactedRegion) : ModuleData :=
  unsafeCast (unsafeCast region : RegionLayout).root

/-- The inspector links this fixed native comparison primitive. Interpreted
callers return zero and retain the serialization check below. The object-valued
Nat result and owned parameters match the interpreter's exported-function ABI. -/
@[noinline, export lean_dtr_mapped_image_match]
private unsafe def mappedImageMatch (_root : NonScalar) (_coordinates : Array USize)
    (_bytes : ByteArray) : Nat := 0

private unsafe def matchesLoadedImage (region : CompactedRegion) (bytes : ByteArray) : Bool :=
  let view : RegionLayout := unsafeCast region
  mappedImageMatch view.root #[view.size, view.baseAddr, view.bufferOffset,
    if view.isMemoryMapped then 1 else 0] bytes == 1

private def loadedIdentity (name : Name) (data : ModuleData) (bytes : ByteArray)
    (region : CompactedRegion) : IO String := do
  if (unsafe ptrEq data (loadedPart region)) && (unsafe matchesLoadedImage region bytes) then
    -- Hash the exact captured image, never a later read of its mutable path.
    return (← capturedHashes #[bytes])[0]!
  IO.FS.withTempFile fun _ path => do
    saveModuleData path name data
    unless (← IO.FS.readBinFile path) == bytes do
      throw <| IO.userError s!"incomplete_closure:E7.loaded_native:{name}"
    return (← fileHashes #[path.toString])[0]!

/-- Re-serialize the original loaded chains, including their cross-part sharing.
Missing private/server/IR regions remain incomplete; disk-only hashes cannot
substitute for a part that was not loaded into this Environment. -/
private def loadedModuleParts (env : Environment) (name : Name) (artifact : System.FilePath) :
    CoreM (Array SourceInput × Array UInt64) := do
  let mut inputs := #[]
  let mut hashes := #[]
  for (key, paths) in #[(name, #[artifact, artifact.addExtension "server",
      artifact.addExtension "private"]),
      (name ++ `ir, #[artifact.withExtension "ir.sig", artifact.withExtension "ir"])] do
    let mut parts : Array ModuleData := #[]
    for path in paths do
      let region ← loadedRegion env path
      parts := parts.push (unsafe loadedPart region)
    let (partInputs, partHashes) ← IO.FS.withTempDir (m := IO) fun temp => do
      let outputs := parts.mapIdx fun i data => (temp / s!"part{i}", data)
      saveModuleDataParts key outputs
      let identities ← fileHashes (outputs.map (·.1.toString))
      let mut inputs := #[]
      let mut hashes := #[]
      for ((input, output), identity) in (paths.zip (outputs.map (·.1))).zip identities do
        let bytes ← IO.FS.readBinFile input
        unless (← IO.FS.readBinFile output) == bytes do
          throw <| IO.userError s!"incomplete_closure:E7.loaded_native:{name}"
        inputs := inputs.push { path := input.toString, sha256 := identity : SourceInput }
        hashes := hashes.push (binaryHash bytes)
      return (inputs, hashes)
    inputs := inputs ++ partInputs
    hashes := hashes ++ partHashes
  return (inputs, hashes)

private def verifyImported (env : Environment) (name : Name)
    (hashes : Std.HashMap Name ExportHash) : CoreM Snapshot := do
  let some index := env.getModuleIdx? name | throwError "incomplete_closure:E7.native_module:{name}"
  let data := env.header.moduleData[index.toNat]!
  let artifact ← moduleFile env name
  let tracePath := artifact.withExtension "trace"
  let source := sourcePath name
  let sourceBytes ← IO.FS.readBinFile source
  let sourceText ← IO.FS.readFile source
  let traceBytes ← IO.FS.readBinFile tracePath
  let trace ← ofExcept <| Json.parse (← IO.FS.readFile tracePath)
  unless trace.getObjValAs? String "schemaVersion" == .ok "2025-09-10" &&
      trace.getObjValAs? Bool "synthetic" == .ok false do
    throwError "incomplete_closure:E7.native_trace_version:{name}"
  let inputs ← field trace "inputs"
  let compiler ← child inputs s!"Lean {Lean.versionStringCore}, commit {Lean.githash}"
  unless (← ofExcept <| traceHash compiler) == textHash Lean.githash do
    throwError "incomplete_closure:E7.native_compiler:{name}"
  let top ← ofExcept <| inputs.getArr?
  let candidates := top.filter fun input =>
    (((input.getArr?).toOption.bind (·[0]?)).bind (·.getStr?.toOption)).any fun caption =>
      caption == source || caption.endsWith ("/" ++ source)
  unless candidates.size == 1 do throwError "incomplete_closure:E7.native_source_input:{name}"
  let pair ← ofExcept <| candidates[0]!.getArr?
  unless pair.size == 2 && (← ofExcept <| traceHash pair[1]!) == textHash sourceText do
    throwError "incomplete_closure:E7.native_source:{name}"
  unless (← ofExcept <| traceHash inputs) ==
      (← ofExcept <| parseHash (← ofExcept <| trace.getObjValAs? String "depHash")) do
    throwError "incomplete_closure:E7.native_trace_integrity:{name}"
  let imports ← child (← child inputs "deps") "imports"
  -- Compare both the captions and hash values against the actual imported DAG;
  -- implementation must retain the ordered caption/value list, not only a count.
  let mut expectedImports : Array (String × UInt64) := #[]
  for imported in data.imports do
    if let some dependency := hashes[imported.module]? then
      let (caption, transitive, artCaption, arts) := importHashes dependency (!data.isModule) imported
      expectedImports := expectedImports.push
        (s!"{imported.module} transitive imports ({caption})", transitive)
      expectedImports := expectedImports.push (s!"{imported.module}:{artCaption}", arts)
  if expectedImports.isEmpty then
    unless (← ofExcept <| traceHash imports) == 1723 do
      throwError "incomplete_closure:E7.native_dependencies:{name}"
  else
    let rows ← ofExcept <| imports.getArr?
    unless rows.size == expectedImports.size do
      throwError "incomplete_closure:E7.native_dependencies:{name}"
    for (row, (caption, hash)) in rows.zip expectedImports do
      let pair ← ofExcept <| row.getArr?
      unless pair.size == 2 && pair[0]!.getStr? == .ok caption &&
          (← ofExcept <| traceHash pair[1]!) == hash do
        throwError "incomplete_closure:E7.native_dependency:{name}:{caption}"
  let (nativeInputs, nativeHashes) ← if data.isModule then loadedModuleParts env name artifact else do
    let bytes ← IO.FS.readBinFile artifact
    let nativeIdentity ← loadedIdentity name data bytes (← loadedRegion env artifact)
    pure (#[{path := artifact.toString, sha256 := nativeIdentity}], #[binaryHash bytes])
  let output ← field trace "outputs"
  let mut parts ← ofExcept <| output.getObjValAs? (Array String) "o"
  unless output.getObjValAs? Bool "m" == .ok data.isModule &&
      parts.size == (if data.isModule then 3 else 1) do
    throwError "incomplete_closure:E7.native_output:{name}"
  if data.isModule then
    parts := parts.push (← ofExcept <| output.getObjValAs? String "rs")
    parts := parts.push (← ofExcept <| output.getObjValAs? String "r")
  for (part, hash) in parts.zip nativeHashes do
    unless (← ofExcept <| parseHash (part.take 16).toString) == hash do
      throwError "incomplete_closure:E7.native_output:{name}"
  let sourceHashes ← capturedHashes #[sourceBytes, traceBytes]
  let result : Snapshot := { data, inputs := #[
    {path := source, sha256 := sourceHashes[0]!},
    {path := tracePath.toString, sha256 := sourceHashes[1]!}] ++ nativeInputs }
  -- Close source/artifact replacement during verification itself.
  unless ← unchanged result.inputs do
    throwError "incomplete_closure:E7.native_input_changed:{name}"
  return result

/-- Subsequent uses compare the immutable snapshot; they never issue a new
snapshot around a changed input in an already-loaded Environment. -/
private partial def collect (env : Environment) (root : Name) (seen : NameSet)
    (names : Array Name) : CoreM (NameSet × Array Name) := do
  if seen.contains root || !repositoryModule root then return (seen, names)
  let seen := seen.insert root
  if root == env.header.mainModule then return (seen, names.push root)
  let imports ← do
    let some index := env.getModuleIdx? root | throwError "incomplete_closure:E7.native_module:{root}"
    pure env.header.moduleData[index.toNat]!.imports
  let mut seen := seen
  let mut names := names
  for imported in imports do
    let (nextSeen, nextNames) ← collect env imported.module seen names
    seen := nextSeen
    names := nextNames
  return (seen, names.push root)

/-- Validate selected source/native input closures. The current module is bound
by its parser input; only explicitly supplied imported owners are traversed.
Cached snapshots cannot be renewed around changed bytes in the same environment. -/
def validate (roots : Array Name) : CoreM Unit := do
  let profiling := (← IO.getEnv "STRATALINT_INSPECTOR_PROFILE") == some "1"
  let started ← if profiling then IO.monoNanosNow else pure 0
  let env ← getEnv
  let mut cache := checked.getState env
  let mut names : NameSet := {}
  for root in roots do
    let closure ← if let some closure := cache.closures[root]? then pure closure else do
      let (_, closure) ← collect env root {} #[]
      pure closure
    cache := { cache with closures := cache.closures.insert root closure }
    for name in closure do names := names.insert name
  let collected ← if profiling then IO.monoNanosNow else pure 0
  let mut exportNanos := 0
  let mut verifyNanos := 0
  let mut fresh := 0
  let mut retainedInputs : Array SourceInput := #[]
  for name in names do
    if name == env.header.mainModule then
      unless (← IO.FS.readFile (sourcePath name)) == (← getFileMap).source do
        throwError "incomplete_closure:E7.current_source:{name}"
      continue
    if let some snapshot := cache.snapshots[name]? then
      let some index := env.getModuleIdx? name
        | throwError "incomplete_closure:E7.native_module:{name}"
      unless (unsafe ptrEq snapshot.data env.header.moduleData[index.toNat]!) do
        throwError "incomplete_closure:E7.native_environment:{name}"
    else
      let beforeExport ← if profiling then IO.monoNanosNow else pure 0
      let (_, next) ← exports env name cache.exports
      cache := { cache with exports := next }
      let beforeVerify ← if profiling then IO.monoNanosNow else pure 0
      let snapshot ← verifyImported env name cache.exports
      cache := { cache with snapshots := cache.snapshots.insert name snapshot }
      if profiling then
        exportNanos := exportNanos + beforeVerify - beforeExport
        verifyNanos := verifyNanos + (← IO.monoNanosNow) - beforeVerify
        fresh := fresh + 1
    let some snapshot := cache.snapshots[name]?
      | throwError "incomplete_closure:E7.native_snapshot:{name}"
    retainedInputs := retainedInputs ++ snapshot.inputs
  let beforeHashes ← if profiling then IO.monoNanosNow else pure 0
  unless ← unchanged retainedInputs do
    throwError "incomplete_closure:E7.native_input_changed"
  modifyEnv fun current => observedInputs.setState (checked.setState current cache)
    (retainedInputs.map (·.path))
  if profiling then
    let finished ← IO.monoNanosNow
    (← IO.getStderr).putStrLn s!"LEAN_INSPECTOR_PROFILE native_roots={roots.size} \
      fresh_modules={fresh} files={retainedInputs.size} closure_ns={collected - started} \
      export_ns={exportNanos} verify_ns={verifyNanos} rehash_ns={finished - beforeHashes} \
      total_ns={finished - started}"

end NativeCoherence

def sourceInputs (env : Environment) (dependencies : Array DependencyIdentity) : CoreM (Array SourceInput) := do
  let policyOwners := #[`LeanInformationAudit.RegistryTypes, `LeanInformationAudit.Registry,
    `LeanInformationAudit.ReadoutProvenance, `LeanInformationAudit.Syntax]
    |>.filter (fun name => (env.getModuleIdx? name).isSome)
  NativeCoherence.validate (#[env.header.mainModule] ++ policyOwners ++ dependencies.map (·.owner))
  let mut paths := policyPaths.push (sourcePath env.header.mainModule)
  for dep in dependencies do
    if dep.owner.toString.startsWith "D5." || dep.owner.toString.startsWith "LeanInformationAudit.Tests." then
      let path := sourcePath dep.owner
      unless paths.contains path do paths := paths.push path
  readSourceInputs (paths.qsort (· < ·))

def sourceIdentity (inputs : Array SourceInput) : String :=
  Sha256.hex (Json.arr (inputs.map fun input => Json.arr #[Json.str input.path, Json.str input.sha256])).compress.toUTF8

/-- Compare retained bytes; never refresh a stale plan by wrapping old olean
contents with hashes from the current source tree. -/
def validateSourceInputs (inputs : Array SourceInput) : CoreM Unit := do
  for input in inputs do
    unless (← readSourceInput input.path) == input do
      throwError "incomplete_closure:E7.stale_source:{input.path}"

end LeanInformationAudit.TemplateAudit

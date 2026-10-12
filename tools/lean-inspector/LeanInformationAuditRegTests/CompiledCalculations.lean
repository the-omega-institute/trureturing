import LeanInformationAudit.ArtifactAssessment
import Lean.Elab.Command

namespace LeanInformationAuditRegTests.CompiledCalculations
open Lean LeanInformationAudit Contract.CompiledExpressions

private def memoTableAgreement [BEq α] [Hashable α] [Inhabited α] (label : String)
    (keys : Array α) (missing : α) : IO Unit := do
  let mut actual : PersistentHashMap α Nat := {}
  let mut expected : Std.HashMap α Nat := {}
  for i in [:keys.size] do
    actual := actual.insert keys[i]! i
    expected := expected.insert keys[i]! i
  let original := actual
  for i in [:keys.size] do
    unless actual.find? keys[i]! == expected[keys[i]!]? do
      throw <| IO.userError s!"compiled.memo_storage:{label}:growth:{i}"
  for i in [:keys.size] do
    if i % 7 == 0 then
      actual := actual.insert keys[i]! (i + keys.size)
      expected := expected.insert keys[i]! (i + keys.size)
  for i in [:keys.size] do
    unless actual.find? keys[i]! == expected[keys[i]!]? &&
        original.find? keys[i]! == some i do
      throw <| IO.userError s!"compiled.memo_storage:{label}:replacement:{i}"
  unless actual.find? missing == none && expected[missing]? == none do
    throw <| IO.userError s!"compiled.memo_storage:{label}:absent"

private structure CollisionKey where
  index : Nat
  deriving BEq, Inhabited

private instance : Hashable CollisionKey := ⟨fun _ => 0⟩

private def memoStorage : IO Unit := do
  let expressions := (Array.range 2049).map fun i => ExprStructEq.mk (mkNatLit i)
  let scopeKeys := fun i => if i % 2 == 0 then #[] else #[ExprStructEq.mk (mkConst ``Nat)]
  memoTableAgreement "heads"
    (expressions.mapIdx fun i e => (e, i % 3 == 0, i % 5 == 0, scopeKeys i))
    (ExprStructEq.mk (mkNatLit 2050), false, false, #[])
  memoTableAgreement "types"
    (expressions.mapIdx fun i e => (e, scopeKeys i))
    (ExprStructEq.mk (mkNatLit 2050), #[])
  memoTableAgreement "propositions"
    (expressions.mapIdx fun i e => (e, scopeKeys i))
    (ExprStructEq.mk (mkNatLit 2050), #[])
  memoTableAgreement "erased"
    ((Array.range 2049).map fun i => (USize.ofNat i, #[USize.ofNat (i % 3)]))
    (USize.ofNat 2050, #[])
  memoTableAgreement "comparisons"
    (expressions.mapIdx fun i e => (e, ExprStructEq.mk (mkNatLit (i + 1)), scopeKeys i))
    (ExprStructEq.mk (mkNatLit 2050), ExprStructEq.mk (mkNatLit 2051), #[])
  memoTableAgreement "full_hash_collisions"
    ((Array.range 32).map fun i => (⟨i⟩ : CollisionKey)) ⟨32⟩
  IO.println "[PASS] compiled.memo_storage: five exact key kinds, growth, replacement, persistence and collisions"

private def memoQueryGrowth (context : Context) : IO Unit := do
  let outerStart ← IO.getNumHeartbeats
  let mut closed : Memo := {}
  let mut lexical : Memo := {}
  let mut maxRaw := 0
  for i in [:1538] do
    let value := mkRawNatLit i
    let type := Expr.sort (.param (.num `memoUniverse i))
    let action := do
      return (← head value, ← typeShape value, ← propositionShape type,
        ← erase value, ← sameShape value (mkRawNatLit (i + 1)))
    let start ← IO.getNumHeartbeats
    let ((h, t, p, e, s), _, nextClosed, nextLexical) ← runScoped
      {context with heartbeatStart := start, heartbeatLimit := 20000} action closed lexical
    let raw := (← IO.getNumHeartbeats) - start
    maxRaw := max maxRaw raw
    unless h == value && t == mkConst ``Nat && !p && e == value && !s && raw ≤ 20000 do
      throw <| IO.userError s!"compiled.memo_query_growth:result_or_raw_budget:{i}:{raw}; \
        head={repr h}; type={repr t}; proposition={p}; erased={repr e}; comparison={s}"
    closed := nextClosed
    lexical := nextLexical
    let ((h', t', p', e', s'), reusedWork, _, _) ← runScoped
      {context with heartbeatStart := (← IO.getNumHeartbeats), heartbeatLimit := 20000}
      action closed lexical
    unless h' == h && t' == t && p' == p && e' == e && s' == s && reusedWork == 5 do
      throw <| IO.userError s!"compiled.memo_query_growth:cached_results:{i}:{reusedWork}"
    unless (← IO.getNumHeartbeats) - outerStart ≤ 100000000 do
      throw <| IO.userError "compiled.memo_query_growth:outer_raw_budget"
  let id : FVarId := ⟨`memoLexical⟩
  let natural := ({} : LocalContext).mkLocalDecl id `x (mkConst ``Nat) .default
  let boolean := ({} : LocalContext).mkLocalDecl id `x (mkConst ``Bool) .default
  let (naturalType, _, shared, naturalMemo) ← runScoped
    {context with local? := natural.find?} (typeShape (mkFVar id)) closed {}
  let (booleanType, _, _, _) ← runScoped
    {context with local? := boolean.find?} (typeShape (mkFVar id)) shared {}
  let (restored, restoredWork, _, _) ← runScoped
    {context with local? := natural.find?} (typeShape (mkFVar id)) shared naturalMemo
  unless naturalType == mkConst ``Nat && booleanType == mkConst ``Bool &&
      restored == naturalType && restoredWork == 1 do
    throw <| IO.userError "compiled.memo_query_growth:lexical_isolation"
  IO.println s!"[PASS] compiled.memo_query_growth: 1538 retained queries, five caches; max_raw={maxRaw}"

run_meta do
  liftM memoStorage
  let env ← getEnv
  let start ← IO.getNumHeartbeats
  liftM <| memoQueryGrowth {
    find := env.find?
    heartbeatStart := start
    heartbeatLimit := 100000000 }

private def decideSamePropositionDifferentInstances (context : Context) : IO Unit := do
  let proposition := mkConst ``True
  let classical := mkApp (mkConst ``Classical.propDecidable) proposition
  let constructive := mkApp2 (mkConst ``Decidable.isTrue) proposition (mkConst ``True.intro)
  let (same, _) ← run context (sameShape
    (mkApp2 (mkConst ``Decidable.decide) proposition classical)
    (mkApp2 (mkConst ``Decidable.decide) proposition constructive))
  unless classical != constructive && same do
    throw <| IO.userError "compiled.decide_same_proposition_different_instances"
  IO.println "[PASS] compiled.decide_same_proposition_different_instances"

private def decideDifferentPropositions (context : Context) : IO Unit := do
  let decision := fun proposition => mkApp2 (mkConst ``Decidable.decide) proposition
    (mkApp (mkConst ``Classical.propDecidable) proposition)
  let (same, _) ← run context
    (sameShape (decision (mkConst ``True)) (decision (mkConst ``False)))
  unless !same do throw <| IO.userError "compiled.decide_different_propositions"
  IO.println "[PASS] compiled.decide_different_propositions"

private def otherInstanceArgumentsRemainSignificant (context : Context) : IO Unit := do
  let first : FVarId := ⟨`firstToString⟩
  let second : FVarId := ⟨`secondToString⟩
  let dictionaryType := mkApp (mkConst ``ToString [0]) (mkConst ``Nat)
  let locals := ({} : LocalContext).mkLocalDecl first `first dictionaryType .instImplicit
    |>.mkLocalDecl second `second dictionaryType .instImplicit
  let value := fun dictionary => mkAppN (mkConst ``ToString.toString [0])
    #[mkConst ``Nat, mkFVar dictionary, mkNatLit 0]
  let (same, _) ← run {context with local? := locals.find?}
    (sameShape (value first) (value second))
  unless !same do throw <| IO.userError "compiled.other_instance_arguments_remain_significant"
  IO.println "[PASS] compiled.other_instance_arguments_remain_significant"

private def sourceOccurrencePaths (context : TemplateAudit.CompiledEnrollment.Context) : IO Unit := do
  let action : CompiledSourceScope.M Unit := do
    let natural := mkConst ``Nat
    let untouched := mkApp2 (mkConst ``Nat.add) (.bvar 0) (.bvar 1)
    let occurrence := mkApp (mkConst ``Not) (.bvar 0)
    let replacement := mkApp2 (mkConst ``Eq [1]) (.bvar 1) occurrence
    let metadata : MData := ⟨[(`source, .ofNat 17)]⟩
    let cases : Array (String × (Expr → Expr) × String × Nat) := #[
      ("app_fn", fun e => .app e untouched, "fn", 1),
      ("app_arg", fun e => .app untouched e, "arg", 1),
      ("forall_domain", fun e => .forallE `x e untouched .implicit, "domain", 1),
      ("forall_body", fun e => .forallE `x (.bvar 0) e .instImplicit, "body", 2),
      ("lambda_domain", fun e => .lam `x e untouched .strictImplicit, "domain", 1),
      ("lambda_body", fun e => .lam `x (.bvar 0) e .default, "body", 2),
      ("let_type", fun e => .letE `x e untouched untouched true, "type", 1),
      ("let_value", fun e => .letE `x (.bvar 0) e untouched false, "value", 1),
      ("let_body", fun e => .letE `x (.bvar 0) untouched e false, "body", 2),
      ("projection", fun e => .proj `Prod 1 e, "body", 1),
      ("metadata", fun e => .mdata metadata e, "body", 1)]
    for (label, wrap, step, size) in cases do
      let source := Expr.forallE `outer natural (wrap occurrence) .default
      let path := #["body", step]
      let (scope, selected) ← CompiledSourceScope.atPath source path
      unless scope.size == size && selected.equal occurrence do
        throw <| IO.userError s!"compiled.source_paths:{label}:selection"
      let changed ← CompiledSourceScope.replaceSourceAt source path.toList replacement
      unless reprStr changed == reprStr (Expr.forallE `outer natural (wrap replacement) .default) do
        throw <| IO.userError s!"compiled.source_paths:{label}:raw_context"
      let restored ← CompiledSourceScope.replaceSourceAt changed path.toList occurrence
      unless reprStr restored == reprStr source do
        throw <| IO.userError s!"compiled.source_paths:{label}:untouched_fields"
      if step != "fn" && step != "arg" then
        let rejected ← try
          discard <| CompiledSourceScope.replaceAt (wrap occurrence) [step] replacement
          pure false
        catch error => pure (error.toString == "unclassified_form:source.state_operand_path")
        unless rejected do throw <| IO.userError s!"compiled.source_paths:{label}:operand_grammar"
    let sibling := Expr.lam `same natural (.bvar 0) .implicit
    let source := Expr.app sibling sibling
    let (left, _) ← CompiledSourceScope.atPath source #["fn", "body"]
    let (right, _) ← CompiledSourceScope.atPath source #["arg", "body"]
    unless left[0]!.path != right[0]!.path do
      throw <| IO.userError "compiled.source_paths:sibling_ancestry"
    let changed ← CompiledSourceScope.replaceSourceAt source ["fn", "body"] replacement
    unless changed.equal (.app (.lam `same natural replacement .implicit) sibling) do
      throw <| IO.userError "compiled.source_paths:sibling_preservation"
    let some owner := context.provenance.view.ownerOf ``Nat.add
      | throw <| IO.userError "compiled.source_paths:fixture_owner"
    let proposition := mkApp3 (mkConst ``Eq [1]) natural
      (mkApp2 (mkConst ``Fin.val) (.bvar 2) (.bvar 0)) (mkNatLit 0)
    let quantify := fun e => Expr.forallE `n natural
      (.forallE `h (mkConst ``True)
        (.forallE `w (mkApp (mkConst ``Fin) (.bvar 1)) e .default) .implicit) .default
    let quantified := ConstantInfo.thmInfo {
      name := ``Nat.add, levelParams := [],
      type := quantify proposition, value := mkConst ``True.intro}
    let scope ← CompiledSourceScope.resolve quantified {
      owner, coordinates := #[0],
      readouts := #[{
        path := #["body", "body", "body"],
        stateOperand := some #["fn", "arg", "arg"], booleanPredicate := true}]}
    let decision := mkApp2 (mkConst ``Decidable.decide) proposition
      (mkApp (mkConst ``Classical.propDecidable) proposition)
    let expected := quantify (mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      decision (mkConst ``Bool.true))
    let some readout := scope.readouts[0]?
      | throw <| IO.userError "compiled.source_paths:quantified_readout_missing"
    unless scope.source.equal quantified.type && scope.expanded.equal expected &&
        scope.telescope.size == 3 && readout.rawObservation.equal proposition do
      throw <| IO.userError "compiled.source_paths:quantified_boolean_reconstruction"
    let inside := Expr.lam `internal natural
      (mkApp3 (mkConst ``Eq [1]) natural (.bvar 0) (.bvar 0)) .default
    let internal := ConstantInfo.thmInfo {
      name := ``Nat.add, levelParams := [],
      type := .forallE `outer natural inside .default, value := mkConst ``True.intro}
    let internalRejected ← try
      discard <| CompiledSourceScope.resolve internal {
        owner, coordinates := #[],
        readouts := #[{
          path := #["body"], stateOperand := some #["body", "arg"],
          booleanPredicate := true}]}
      pure false
    catch error => pure (error.toString == "unclassified_form:source.state_operand_scope")
    unless internalRejected do throw <| IO.userError "compiled.source_paths:internal_operand_binder"
    let info := ConstantInfo.thmInfo {
      name := ``Nat.add, levelParams := [],
      type := source, value := mkConst ``True.intro}
    let captured ← try
      discard <| CompiledSourceScope.resolve info {
        owner, coordinates := #[0],
        readouts := #[{path := #["fn", "body"], stateBinder := 0},
          {path := #["arg", "body"], stateBinder := 0}]}
      pure false
    catch error => pure (error.toString == "unclassified_form:source.captured_coordinate")
    unless captured do throw <| IO.userError "compiled.source_paths:captured_coordinate"
    for path in #[#["domain"], #["arg", "value"], #["fn", "body", "body"]] do
      let selected ← try
        discard <| CompiledSourceScope.atPath source path
        pure false
      catch error => pure (error.toString == "unclassified_form:source.absent_occurrence")
      let replaced ← try
        discard <| CompiledSourceScope.replaceSourceAt source path.toList replacement
        pure false
      catch error => pure (error.toString == "unclassified_form:source.absent_occurrence")
      unless selected && replaced do throw <| IO.userError "compiled.source_paths:malformed"
    let binders : Array SourceBinder := #[{name := `n, info := .default, domain := natural},
      {name := `x, info := .default, domain := mkApp (mkConst ``Fin) (.bvar 0)}]
    let dependent := Expr.lam `internal (.bvar 1) (mkApp (.bvar 2) (.bvar 0)) .default
    let transported ← CompiledSourceScope.transport binders #[0] dependent
    unless transported.equal (.lam `internal (.bvar 0) (mkApp (.bvar 1) (.bvar 0)) .default) do
      throw <| IO.userError "compiled.source_paths:dependent_internal_references"
    let missing ← try
      discard <| CompiledSourceScope.transport (binders.extract 0 1) #[] binders[1]!.domain
      pure false
    catch error => pure (error.toString.startsWith "unclassified_form:source.coordinate_dependency:")
    unless missing do throw <| IO.userError "compiled.source_paths:missing_dependency"
    let deep := (List.range 257).foldl (fun e _ => Expr.mdata metadata e) occurrence
    let bounded ← try
      discard <| CompiledSourceScope.replaceSourceAt deep (List.replicate 257 "body") replacement
      pure false
    catch error => pure (error.toString == "incomplete_closure:E8.source_path")
    unless bounded do throw <| IO.userError "compiled.source_paths:path_limit"
  discard <| (action.run 524288).run context
  let exhausted ← try
    discard <| ((CompiledSourceScope.replaceSourceAt (mkConst ``True) []
      (mkConst ``False)).run 0).run context
    pure false
  catch error => pure (error.toString == "incomplete_closure:E8.source_work")
  unless exhausted do throw <| IO.userError "compiled.source_paths:work_limit"
  IO.println "[PASS] compiled.source_paths: all raw constructors, lexical references and rejection guards"

unsafe def check (reader : IO.Ref RawArtifacts.Store) : IO Unit := do
  RawArtifacts.loadModule `LeanInformationAudit.TemplateEnrollment reader
  let store ← reader.get
  let context := CompiledRegistration.expressionContext (store.constants.find?)
    (← IO.getNumHeartbeats) {}
  decideSamePropositionDifferentInstances context
  decideDifferentPropositions context
  otherInstanceArgumentsRemainSignificant context
  let value := mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 3)
  let ((first, same), work) ← run context (do
    let first ← erase value
    let mut same := true
    for size in [:100] do
      let next ← erase value (Array.replicate size (mkConst ``Bool))
      same := same && next == first
    return (first, same))
  unless first == value && same && work < 1000 do
    throw <| IO.userError s!"compiled.closed_context_memo:{work}"
  let (_, initialWork, memo) ← runCached context (erase value) {}
  let (again, reusedWork, _) ← runCached context (erase value) memo
  unless again == first && reusedWork == 1 && reusedWork < initialWork do
    throw <| IO.userError "compiled.closed_query_memo"
  let tooDeep ← try
    discard <| runCached context (erase value (depth := 256)) memo
    pure false
  catch _ => pure true
  unless tooDeep do throw <| IO.userError "compiled.memo_depth_limit"
  let id : FVarId := ⟨`sameLocal⟩
  let locals := ({} : LocalContext).mkLocalDecl id `x (mkConst ``Nat) .default
  let (_, _, memo) ← runCached {context with local? := locals.find?} (typeShape (mkFVar id)) memo
  let changedLocals := ({} : LocalContext).mkLocalDecl id `x (mkConst ``Bool) .default
  let (changedType, _, _) ← runCached {context with local? := changedLocals.find?}
    (typeShape (mkFVar id)) memo
  unless changedType == mkConst ``Bool do
    throw <| IO.userError "compiled.lexical_query_isolation"
  let localContext := { context with local? := locals.find? }
  let (apart, _) ← run localContext (sameShape (mkFVar id) (mkNatLit 0))
  let (discarded, _) ← run localContext
    (sameShape (mkApp (.lam `x (mkConst ``Nat) (mkNatLit 0) .default) (mkFVar id)) (mkNatLit 0))
  let proofLocals := ({} : LocalContext).mkLocalDecl id `h (mkConst ``True) .default
  let (proofSame, _) ← run { context with local? := proofLocals.find? }
    (sameShape (mkFVar id) (mkConst ``True.intro))
  unless !apart && discarded && proofSame do
    throw <| IO.userError "compiled.local_neutral:closed_terms_and_proof_irrelevance"
  let expensive := mkApp2 (mkConst ``Nat.decEq) (mkNatLit 2520) (mkNatLit 2519)
  let (differentTypes, _) ← run context (sameShape (mkNatLit 0) expensive) 256
  unless !differentTypes do
    throw <| IO.userError "compiled.comparison:rigid_types_before_data"
  let neutralRecursor := mkAppN (mkConst ``Nat.rec [1]) #[
    .lam `index (mkConst ``Nat) (mkConst ``Nat) .default,
    mkRawNatLit 0,
    .lam `index (mkConst ``Nat) (.lam `previous (mkConst ``Nat) (mkRawNatLit 1) .default)
      .default,
    mkFVar id]
  let (blocked, _) ← run localContext
    (sameShape neutralRecursor (mkApp2 (mkConst ``Nat.gcd) (mkNatLit 2520) (mkNatLit 1))) 256
  let letLocals := ({} : LocalContext).mkLetDecl id `x (mkConst ``Nat) (mkRawNatLit 0)
  let (reduced, _) ← run {context with local? := letLocals.find?}
    (sameShape neutralRecursor (mkRawNatLit 0)) 256
  unless !blocked && reduced do
    throw <| IO.userError "compiled.comparison:neutral_data_recursor_and_local_let"
  let sourceType := Expr.bvar 0
  let targetType := mkApp (.lam `value (mkConst ``Nat) (.bvar 0) .default) sourceType
  let transport := mkAppN (mkConst ``Eq.rec [1, 1]) #[
    mkConst ``Nat, sourceType, mkLambda `value .default (mkConst ``Nat)
      (mkLambda `proof .default (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (.bvar 1) (.bvar 0))
        (mkConst ``Nat)), mkNatLit 7, targetType,
    TemplateAudit.proofPlaceholder
      (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) sourceType targetType)]
  let (transported, _) ← run context (head transport (binders := #[mkConst ``Nat]))
  unless transported == mkRawNatLit 7 do
    throw <| IO.userError "compiled.comparison:equality_transport_binder_scope"
  let fingerprint := fun e => IO.ofExcept (TemplateAudit.compactRawIdentity [] e)
  let repeated := (List.range 18).foldl
    (fun term _ => mkApp2 (mkConst ``Nat.add) term term) value
  let .ok (_, repeatedWork) := TemplateAudit.compactRawIdentity [] repeated 4096
    | throw <| IO.userError "compiled.identity:shared_dag_work"
  unless repeatedWork < 4096 do throw <| IO.userError "compiled.identity:shared_dag_limit"
  let (original, _) ← fingerprint value
  let (changed, _) ← fingerprint (mkApp2 (mkConst ``Nat.add) (mkNatLit 2) (mkNatLit 4))
  unless original != changed do
    throw <| IO.userError "compiled.identity:changed_argument"
  let lambda := Expr.lam `a (mkConst ``Nat) (.bvar 0) .default
  let (renamed, _) ← fingerprint (.lam `b (mkConst ``Nat) (.bvar 0) .default)
  let (explicit, _) ← fingerprint lambda
  let (implicit, _) ← fingerprint (.lam `a (mkConst ``Nat) (.bvar 0) .implicit)
  unless renamed == explicit && explicit != implicit do
    throw <| IO.userError "compiled.identity:binder_annotation"
  let marked := fun (position : Nat) => Expr.mdata
    ⟨[(`source, .ofSyntax (.atom (.synthetic ⟨position⟩ ⟨position + 1⟩ false) "token"))]⟩ value
  let ((sourceA, sourceB), _) ← run context do
    let first ← erase (marked 0)
    let second ← erase (marked 1)
    return (first, second)
  unless (← fingerprint sourceA).1 != (← fingerprint sourceB).1 do
    throw <| IO.userError "compiled.identity:raw_metadata_source_bytes"
  let deep := (List.range 257).foldl (fun body _ => Expr.lam `a (mkConst ``Nat) body .default)
    (mkNatLit 0)
  unless (match TemplateAudit.compactRawIdentity [] deep with
      | .error _ => true | .ok _ => false) do
    throw <| IO.userError "compiled.identity:depth_limit"
  let enrollment ← TemplateAudit.CompiledEnrollment.Context.fromArtifacts store
    `LeanInformationAudit.TemplateEnrollment {} {}
  sourceOccurrencePaths enrollment
  let query := fun locals =>
    (RegistrationGates.compiledQueryWork (typeShape (mkFVar id))).run
      { enrollment.provenance with locals }
  let (naturalType, _) ← query locals
  let (booleanType, _) ← query changedLocals
  let (restoredType, restoredWork) ← query locals
  unless naturalType == mkConst ``Nat && booleanType == mkConst ``Bool &&
      restoredType == naturalType && restoredWork == 1 do
    throw <| IO.userError "compiled.session:lexical_scope_identity"
  unless !enrollment.pins.isEmpty && enrollment.pins.all (fun pin =>
      (store.owners.find? pin.identity.name) == some pin.identity.owner) do
    throw <| IO.userError "compiled.dictionary:owner_identity"
  IO.println s!"[PASS] compiled calculations: closed context work={work}; \
    complete identities, binder annotations, depth and dictionary owners"


end LeanInformationAuditRegTests.CompiledCalculations

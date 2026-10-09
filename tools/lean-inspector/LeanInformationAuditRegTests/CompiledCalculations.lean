import LeanInformationAudit.ArtifactAssessment

namespace LeanInformationAuditRegTests.CompiledCalculations
open Lean LeanInformationAudit Contract.CompiledExpressions

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

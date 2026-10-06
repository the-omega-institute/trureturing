import LeanInformationAudit.ArtifactAssessment

namespace LeanInformationAuditRegTests.CompiledCalculations
open Lean LeanInformationAudit Contract.CompiledExpressions

unsafe def check : IO Unit := do
  let reader ← IO.mkRef ({} : RawArtifacts.Store)
  RawArtifacts.loadModule `LeanInformationAudit.TemplateEnrollment reader
  let store ← reader.get
  let context := CompiledRegistration.expressionContext (store.constants[·]?)
    (← IO.getNumHeartbeats) {}
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
      (store.owners[pin.identity.name]?) == some pin.identity.owner) do
    throw <| IO.userError "compiled.dictionary:owner_identity"
  IO.println s!"[PASS] compiled calculations: closed context work={work}; \
    complete identities, binder annotations, depth and dictionary owners"

run_meta check

end LeanInformationAuditRegTests.CompiledCalculations

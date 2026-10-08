import LeanInformationAudit.ArtifactAssessment

namespace LeanInformationAuditRegTests.CompiledSeal
open Lean LeanInformationAudit

unsafe def check (reader : IO.Ref RawArtifacts.Store) : IO Unit := do
  let fixturePath ← Repository.source ".lake/build/lean-inspector/reg/lib/lean"
  let saved ← searchPathRef.get
  searchPathRef.set (fixturePath :: saved)
  try
    let root := `Reg.Catalogs.PointwiseDisequalityRegistrations.SealedCatalog
    RawArtifacts.loadModule root reader
    RawArtifacts.loadModule `LeanInformationAudit.TemplateEnrollment reader
    let store ← reader.get
    let context := CompiledRegistration.expressionContext (store.constants[·]?) (← IO.getNumHeartbeats) {}
    let transport (left right : Expr) : Expr := mkAppN (mkConst ``Eq.rec [1, 1]) #[
      mkSort 1, left, mkLambda `type .default (mkSort 1)
        (mkLambda `proof .default (mkApp3 (mkConst ``Eq [1]) (mkSort 1) left (.bvar 0))
          (mkConst ``Nat)), mkNatLit 7, right,
      TemplateAudit.proofPlaceholder (mkApp3 (mkConst ``Eq [1]) (mkSort 1) left right)]
    let (same, _) ← Contract.CompiledExpressions.run context
      (Contract.CompiledExpressions.head (transport (mkConst ``Nat) (mkConst ``Nat)))
    let (different, _) ← Contract.CompiledExpressions.run context
      (Contract.CompiledExpressions.head (transport (mkConst ``Nat) (mkConst ``Bool)))
    unless (Contract.Literal.nat "transport" same).toOption == some 7 &&
        different.isAppOf ``Eq.rec do
      throw <| IO.userError "compiled.transport:invalid_endpoint_behavior"
    let (state, seals) ← ArtifactAssessment.assess store root
    unless seals.size == 1 && seals.all (fun sealRecord =>
        sealRecord.compiledEvidence && sealRecord.catalog.units.size == 2) do
      throw <| IO.userError "compiled.seal:complete_unit_membership"
    let snapshot ← ArtifactAssessment.discover store root
    let some (_, contract) := snapshot.roots.find? (·.2.rootId == root)
      | throw <| IO.userError "compiled.seal:root_missing"
    let entries := ArtifactRegistration.entriesFor state root
    let missing := { contract with expected := contract.expected.extract 1 contract.expected.size }
    let result := CompiledSnapshots.registry (state.store.constants[·]?) root (some missing) entries
    unless (match result with
        | .error reason => (reason.splitOn "component=member-set").length == 2
        | .ok _ => false) do
      throw <| IO.userError "compiled.seal:missing_member_accepted"
    let some first := contract.source[0]?
      | throw <| IO.userError "compiled.seal:source_missing"
    let baseline := { contract with baseline := #[{ first with registrationModuleName := `otherContributor }] }
    let result := CompiledSnapshots.registry (state.store.constants[·]?) root (some baseline) entries
    unless (match result with
        | .error reason => (reason.splitOn "component=frozen-baseline-contributor-modules").length == 2
        | .ok _ => false) do
      throw <| IO.userError "compiled.seal:baseline_contributor_accepted"
    -- The seal vector must match every imported registration;
    -- snapshot set checks alone cannot detect a repeated vector operand.
    let some (_, input) := snapshot.seals.find? (·.1 == root)
      | throw <| IO.userError "compiled.seal:input_missing"
    let some firstCatalog := input.catalogs[0]?
      | throw <| IO.userError "compiled.seal:catalog_missing"
    let raw ← Contract.Decoder.referencedValue (state.store.constants[·]?) firstCatalog.value
    let fields ← Contract.Decoder.fields (state.store.constants[·]?) `LeanInformationAudit.Contract.SealCatalog raw 11
    let duplicate := mkLambda `index .default (mkApp (mkConst ``Fin) fields[3]!)
      (mkApp fields[4]! (CompiledSeal.indexValue 0 2))
    let arguments := raw.getAppArgs
    let mutatedValue := mkAppN raw.getAppFn (arguments.set! (arguments.size - 11 + 4) duplicate)
    let mutated := { firstCatalog with value := mutatedValue }
    let wrong := { input with catalogs := #[mutated] }
    let rejected ← try
      discard <| (CompiledSeal.consume snapshot root wrong).run state
      pure false
    catch error => pure (((toString error).splitOn "component=reg-vector:").length == 2)
    unless rejected do throw <| IO.userError "compiled.seal:duplicate_vector_operand_accepted"
    IO.println "[PASS] compiled seal: complete real catalog membership and snapshot rejections"
    let sharedRoot := `Reg.Catalogs.SharedInformationRoot.SealedCatalog
    RawArtifacts.loadModule sharedRoot reader
    let (_, sharedSeals) ← ArtifactAssessment.assess (← reader.get) sharedRoot
    let own := sharedSeals.filter (·.catalog.rootId == sharedRoot)
    unless own.size == 12 && own.all (·.compiledEvidence) &&
        own.foldl (fun count row => count + row.catalog.units.size) 0 == 13 do
      throw <| IO.userError "compiled.seal:shared_unit_membership"
    IO.println "[PASS] compiled shared seal: 12 catalogs and 13 exact imported units"
  finally searchPathRef.set saved

end LeanInformationAuditRegTests.CompiledSeal

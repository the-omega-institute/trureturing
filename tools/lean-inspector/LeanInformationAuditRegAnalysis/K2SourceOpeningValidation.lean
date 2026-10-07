import LeanInformationAuditRegAnalysis.K2HeadFamiliesGenerator

open Lean

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let input ← match args with
    | [input] => pure input
    | _ => throw <| IO.userError "SMALL_SELECTOR_JSON required"
  let data ← IO.ofExcept <| Json.parse (← IO.FS.readFile input)
  let modules ← IO.ofExcept <| (← IO.ofExcept <| data.getObjVal? "modules").getArr? >>= fun values =>
    values.mapM fun value => return (← value.getStr?).toName
  let rows ← IO.ofExcept <| (← IO.ofExcept <| data.getObjVal? "rows").getArr?
  let opts := ({} : Options).set `maxHeartbeats (200000 : Nat)
  enableInitializersExecution
  let imports := modules.map fun module => ({ module, importAll := true } : Import)
  let env ← importModules (imports.push {
    module := `LeanInformationAuditRegAnalysis.K2HeadFamiliesGenerator,
    importAll := true }) opts (loadExts := true)
  let validate : Lean.MetaM Unit := do
    K2HeadFamiliesGenerator.resetCompletedHeads
    K2FactsGenerator.rawBindingKeys.set {}
    let first := Expr.lam `left (mkConst ``Nat) (.bvar 0) .default
    let second := Expr.lam `right (mkConst ``Nat) (.bvar 0) .default
    let type := Expr.forallE `domain (mkConst ``Nat) (mkConst ``Nat) .default
    let renamedType := Expr.forallE `renamedDomain (mkConst ``Nat) (mkConst ``Nat) .default
    unless first.hash == second.hash && !first.equal second &&
        type.hash == renamedType.hash && !type.equal renamedType do
      throwError "key_cache_control.raw_collision_precondition"
    let levelOperand := mkConst `K2RawCoordinateLevels []
    let bucketHash := mixHash (mixHash first.hash type.hash) levelOperand.hash
    let firstKey ← K2FactsGenerator.rawBindingKey first type []
    let secondKey ← K2FactsGenerator.rawBindingKey second type []
    unless firstKey == s!"raw:{bucketHash}:0" && secondKey == s!"raw:{bucketHash}:1" do
      throwError "key_cache_control.collision_bucket_order"
    let firstHit ← K2FactsGenerator.rawBindingKey first type []
    let secondHit ← K2FactsGenerator.rawBindingKey second type []
    unless firstHit == firstKey && secondHit == secondKey do
      throwError "key_cache_control.exact_hit"
    let changedTypeKey ← K2FactsGenerator.rawBindingKey first renamedType []
    unless changedTypeKey == s!"raw:{bucketHash}:2" do
      throwError "key_cache_control.changed_raw_type"
    let changedLevelsKey ← K2FactsGenerator.rawBindingKey first type [.param `u]
    unless changedLevelsKey != firstKey && changedLevelsKey != secondKey &&
        changedLevelsKey != changedTypeKey do
      throwError "key_cache_control.changed_levels"
    let changedTypeHit ← K2FactsGenerator.rawBindingKey first renamedType []
    let changedLevelsHit ← K2FactsGenerator.rawBindingKey first type [.param `u]
    let firstAgain ← K2FactsGenerator.rawBindingKey first type []
    let secondAgain ← K2FactsGenerator.rawBindingKey second type []
    unless changedTypeHit == changedTypeKey && changedLevelsHit == changedLevelsKey &&
        firstAgain == firstKey && secondAgain == secondKey do
      throwError "key_cache_control.insertion_order_reuse"
    let bucket := ((← K2FactsGenerator.rawBindingKeys.get).find? bucketHash).getD #[]
    unless bucket.size ≥ 3 do throwError "key_cache_control.bucket_missing"
    let (value0, type0, levels0) := bucket[0]!
    let (value1, type1, levels1) := bucket[1]!
    let (value2, type2, levels2) := bucket[2]!
    unless value0.equal first && type0.equal type && levels0.equal levelOperand &&
        value1.equal second && type1.equal type && levels1.equal levelOperand &&
        value2.equal first && type2.equal renamedType && levels2.equal levelOperand do
      throwError "key_cache_control.raw_bucket_contents"
    K2FactsGenerator.rawBindingKeys.set {}
    IO.println "key_cache_control hit_collision_type_levels_order=passed"
    K2HeadFamiliesGenerator.validateClosedSourceReuse
    for row in rows do K2HeadFamiliesGenerator.validateSourceOpening row
    let (hits, misses) ← K2HeadFamiliesGenerator.sourcePathReuse.get
    IO.println s!"opening_control_reuse hits={hits} misses={misses}"
    unless hits > 0 && misses > 0 do throwError "opening_control.missing_hit_or_miss"
    K2HeadFamiliesGenerator.resetCompletedHeads
    unless (← K2HeadFamiliesGenerator.sourcePaths.get).isEmpty &&
        (← K2HeadFamiliesGenerator.sourceTypes.get).isEmpty &&
        (← K2HeadFamiliesGenerator.completedHeads.get).isEmpty &&
        (← K2HeadFamiliesGenerator.closedSources.get).isEmpty &&
        (← K2HeadFamiliesGenerator.sourceContextIDs.get) == 1 do
      throwError "opening_control.reset_failed"
  validate.run' |>.toIO'
    { fileName := "k2-opening-control", fileMap := default, options := opts }
    { env := env.setExporting false }

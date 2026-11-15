import LeanInformationAuditRegAnalysis.SearchReduction.Commands
import LeanInformationAuditRegTests.SearchReduction.LookupBaseline

/-! Recall, nonrecursive closure and incomplete-basis regression checks. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction
open LeanInformationAudit.Tests.SearchReduction.LookupBaseline
set_option Elab.async false
set_option maxHeartbeats 0

run_cmd do
  let name := `PlaceholderFixture.member
  let constant : ConstantVal := {name, levelParams := [], type := mkConst ``True}
  let placeholder : ConstantInfo := .axiomInfo {constant with isUnsafe := false}
  let theoremInfo : ConstantInfo := .thmInfo {constant with value := mkConst ``True.intro}
  let unsafeInfo : ConstantInfo := .defnInfo {
    constant with value := mkConst ``True.intro, hints := .opaque, safety := .unsafe}
  let other : ConstantInfo := .thmInfo {
    constant with name := `PlaceholderFixture.other, value := mkConst ``True.intro}
  let parts := #[#[placeholder, other], #[placeholder, unsafeInfo], #[theoremInfo, theoremInfo]]
  let entries := DiskLookup.membershipEntries "Fixture" parts
  unless entries.size == 2 && entries[0]!.leanName == other.name &&
      entries[0]!.ordinal == 2 && entries[1]!.leanName == name && entries[1]!.ordinal == 1 do
    throwError "placeholder/unsafe copy shadowed the safe theorem or changed declaration ordinals"
  unless (DiskLookup.membershipEntries "Fixture" #[#[placeholder, unsafeInfo]]).isEmpty do
    throwError "ineligible copies entered membership"
  let owners := entries ++ DiskLookup.membershipEntries "OtherOwner" parts
  unless owners.size == 4 && owners[1]!.module != owners[3]!.module do
    throwError "distinct membership owners were collapsed"
  logInfo "LOOKUP_MEMBERSHIP synthetic_placeholder=true unsafe_shadow=true dedup=true ordinals=true owners=true"

run_cmd do
  let directory : System.FilePath :=
    "build/lean-inspector/search-reduction-test-index/placeholder-fixture"
  let storage := directory / "members"
  IO.FS.createDirAll storage
  let plan := directory / "plan.json"
  let resultPath := directory / "result.json"
  IO.FS.writeFile plan (toJson ({modules := #["Std.Data.ExtDTreeMap.Basic"]} :
    DiskLookup.ShardPlan)).compress
  DiskLookup.produceMembershipShard storage plan resultPath
  let result : DiskLookup.MembershipShardResult ← IO.ofExcept <|
    fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile resultPath))
  unless result.missing.isEmpty do throwError "placeholder fixture indexing incomplete"
  liftTermElabM do
    let env := (← getEnv).setExporting false
    let header : DiskLookup.Header := {
      basis := "placeholder-fixture", mathlib := "fixture", inputs := 0,
      storage := "implication", root := "", digest := 0, complete := true,
      modules := 1, declarations := result.indexed, indexed := result.indexed, missing := #[]}
    let index : DiskLookup.Index := {
      directory := directory / "implication", header, manifest := #[],
      membership? := some {
        inputs := 0, storage := "members", complete := true,
        indexed := result.indexed}}
    withEnv env do
      for name in #[`Std.ExtDTreeMap.getEntryLE._proof_1, `Std.ExtDTreeMap.getEntryGE._proof_1] do
        let info ← getConstInfo name
        unless DiskLookup.membershipEligible info do throwError "fixture theorem is ineligible"
        checkLocalProof info.type (mkConst name (info.levelParams.map Level.param))
        let hits ← DiskLookup.queryMembership index info.type
        unless hits.complete && hits.entries.any (·.leanName == name) do
          throwError "complete membership omitted placeholder-shadowed theorem {name}"
        let root ← mkFreshExprMVar info.type
        let trace ← lookupExact {environment := env, disk? := some index} root.mvarId!
        unless trace.complete && trace.source?.isSome && (← root.mvarId!.isAssigned) do
          throwError "production exact lookup lost placeholder-shadowed theorem {name}"
        checkLocalProof info.type (← instantiateMVars root)
        logInfo "LOOKUP_MEMBERSHIP placeholder_shadow=true exact_hit=true kernel=true std3=true"

run_cmd liftTermElabM do
  let left ← Term.elabType (← `(∀ renamed : Nat, Mark renamed ∧ Side))
  let right ← Term.elabType (← `(∀ {n : Nat}, (let x := n; Mark x) ∧ Side))
  Term.synthesizeSyntheticMVarsNoPostponing
  let left ← instantiateMVars left
  let right ← instantiateMVars right
  unless (← DiskLookup.membershipKey left) == (← DiskLookup.membershipKey right) do
    throwError "membership lost alpha/beta/zeta or binder-annotation invariance"
  let index ← DiskLookup.openFixtureIndex
    "build/lean-inspector/search-reduction-test-index/lookup-fixture" "lookup-fixture"
    "56a005855ea17e0b0958f73ec801ae140b0a1679"
  let hits ← DiskLookup.queryMembership index left
  unless hits.complete && hits.entries.any (·.leanName == ``pair) do
    throwError "membership failed to recall the complete renamed statement"
  let some header := index.membership? | throwError "membership header missing"
  let key ← DiskLookup.membershipKey left
  let file := index.directory.parent.getD index.directory / header.storage /
    s!"members-{key.toNat % 256}.pickle"
  let withheld := file.addExtension "withheld"
  IO.FS.rename file withheld
  let missing ← try DiskLookup.queryMembership index left
    finally IO.FS.rename withheld file
  unless !missing.complete do throwError "missing membership bucket certified NoHit"
  let absent ← DiskLookup.queryMembership {index with membership? := none} left
  unless !absent.complete do throwError "missing membership header certified NoHit"
  let privateType ← Term.elabType (← `(∀ n : Nat, PrivateMark n))
  Term.synthesizeSyntheticMVarsNoPostponing
  let privateType ← instantiateMVars privateType
  let privateHits ← DiskLookup.queryMembership index privateType
  let privateEntry := privateHits.entries.find? (·.name.endsWith ".hiddenMember")
  unless privateHits.complete && privateEntry.isSome do
    throwError "complete membership omitted a private theorem"
  let privateInfo ← getConstInfo privateEntry.get!.leanName
  unless DiskLookup.membershipEligible privateInfo &&
      LazyDiscrTree.blacklistInsertion (← getEnv) privateInfo.name do
    throwError "private regression no longer distinguishes membership from suggestions"
  logInfo "LOOKUP_MEMBERSHIP private=true suggestion_blacklist_ignored=true"
  logInfo "LOOKUP_MEMBERSHIP alpha=true normalized=true missing_bucket=unknown missing_header=unknown"

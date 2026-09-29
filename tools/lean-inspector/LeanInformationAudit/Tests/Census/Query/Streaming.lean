import LeanInformationAudit.Census.Membership

open Lean LeanInformationAudit CensusStream

private def theoremInfo : ConstantInfo := .thmInfo {
  name := `Fixture.target, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }

run_cmd do
  let data : ModuleData := { (default : ModuleData) with
    constNames := #[theoremInfo.name], constants := #[theoremInfo] }
  unless CensusOwnership.moduleContainsTheorem data theoremInfo do
    throwError "streamMembershipPositive: theorem not found in its module"
  let malformed := { data with constNames := #[] }
  if CensusOwnership.moduleContainsTheorem malformed theoremInfo then
    throwError "streamMembershipMalformed: missing name table accepted"
  let encoded := toExpr (`Fixture.target : Name)
  unless decodeName? encoded == some `Fixture.target do
    throwError "streamNamedKeyPositive: literal Name did not decode"
  unless (decodeName? (mkConst `opaqueName)).isNone do
    throwError "streamUnclassifiableNamedKey: opaque key silently classified"
  let family := mkApp (mkConst `LeanInformationAudit.BoundedTruncationFamily) (mkConst ``True)
  unless evidenceHead { theoremInfo.toConstantVal with type := family } ==
      some `LeanInformationAudit.BoundedTruncationFamily do
    throwError "streamTypeHeads: direct family evidence not indexed"
  logInfo "streamMembershipPositive streamMembershipMalformed streamNamedKeyPositive streamUnclassifiableNamedKey streamTypeHeads"

run_cmd do
  let left := Json.mkObj [("statement_id", toJson "left-statement")]
  let right := Json.mkObj [("statement_id", toJson "right-statement")]
  let records := Std.HashMap.ofArray #[ ("Left", left), ("Right", right) ]
  unless resolveCollision records "left-statement" == #["Left"] &&
      resolveCollision records "right-statement" == #["Right"] do
    throwError "streamStatementCollisionPositive"
  unless (resolveCollision records "missing").isEmpty do
    throwError "streamStatementCollisionUnresolved"
  let ambiguous := Std.HashMap.ofArray #[ ("Left", left), ("Right", left) ]
  unless (resolveCollision ambiguous "left-statement").size == 2 do
    throwError "streamStatementCollisionAmbiguous"
  logInfo "streamStatementCollisionPositive streamStatementCollisionUnresolved streamStatementCollisionAmbiguous"

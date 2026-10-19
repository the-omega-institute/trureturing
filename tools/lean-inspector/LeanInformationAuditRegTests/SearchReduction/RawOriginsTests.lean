import Mathlib
import LeanInformationAuditRegTests.SearchReduction.SingleSourceModel
import LeanInformationAuditRegTests.SearchReduction.PresentationBaseline

/-! Production-import rejection probes read raw compiled data only. -/
namespace LeanInformationAudit.Tests.SearchReduction.RawOriginsTests
open Lean Meta Elab LeanInformationAudit.SearchReduction

run_elab do
  let env ← getEnv
  let type := (← getConstInfo
    ``LeanInformationAudit.Tests.SearchReduction.PresentationBaseline.ramp_value).type
  let atoms ← match normalizedAtoms env type with
    | .ok atoms => pure atoms
    | .error err => throwError "target normalization: {err}"
  for suffix in #["Circle.path_self", "Circle.range_path_ssubset_univ",
      "blastDivSubtractShift._proof_8", "card_derangements_fin_add_two"] do
    let mut count : Nat := 0
    for (name, info) in env.constants.toList do
      if name.toString.endsWith suffix then
        let bound := (rawOrigins env info.type).run' {}
        if rawNecessary env atoms bound then
          throwError "unrelated production declaration passed raw filter: {name}"
        count := count + 1
    unless count > 0 do throwError "production rejection fixture missing: {suffix}"
    logInfo m!"production raw rejection: {suffix}, declarations={count}, normalizations=0"
end LeanInformationAudit.Tests.SearchReduction.RawOriginsTests

import Mathlib
import LeanInformationAuditRegAnalysis.SearchReduction.Presentation
import LeanInformationAuditRegTests.SearchReduction.SingleSourceModel
import LeanInformationAuditRegTests.SearchReduction.PresentationBaseline

/-! Production-import rejection probes read raw compiled data only. -/
namespace LeanInformationAudit.Tests.SearchReduction.RawOriginsTests
open Lean Meta Elab LeanInformationAudit.SearchReduction

opaque modulusInput : Nat := 7

run_elab do
  let env ← getEnv
  let type := (← getConstInfo
    ``LeanInformationAudit.Tests.SearchReduction.PresentationBaseline.ramp_value).type
  let atoms ← match normalizedAtoms env type with
    | .ok atoms => pure atoms
    | .error err => throwError "target normalization: {err}"
  let closedArithmetic := mkApp2 (mkConst ``Nat.lt)
    (mkApp2 (mkConst ``Nat.mod) (mkConst ``modulusInput) (mkNatLit 2)) (mkNatLit 2)
  match normalizedAtoms env closedArithmetic with
  | .error err => throwError "generated numeral/domain constants became source anchors: {err}"
  | .ok _ => logInfo "closed arithmetic source: generated domain constants are not anchors"
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

run_elab do
  unless standardAxioms (← Lean.collectAxioms ``neutralFirst_complete) do
    throwError "neutral ordering coverage has nonstandard axioms"
  let target ← Term.elabTerm (← `(∀ n : Nat, 0 < n + 1 ∧ True)) (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let env ← getEnv
  let index ← factIndex
  let (outcome, evidence, detail) ← baselinePresentation env [] target (some index)
  unless outcome == .found && evidence.isSome do
    throwError "production neutral presentation: {reprStr outcome}: {detail}"
  logInfo m!"production neutral presentation: found; {detail}"
end LeanInformationAudit.Tests.SearchReduction.RawOriginsTests

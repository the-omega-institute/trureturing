import LeanInformationAudit.Tests.RegistrationGates.AllowlistBoundaries

open Lean LeanInformationAudit.RegistrationGates
namespace ProvenanceIsolation

universe u
inductive Box where
  | mk (_ : PLift (∀ α : Sort u, α = α)) (_ : Bool) : Box

theorem universeTarget : ∀ α : Type, α = α := fun _ => rfl

-- Each withEnv starts with the same imported, compilation-local empty cache.
-- Reordered runs exercise failed queries both before and after a warmed query.
run_cmd Elab.Command.liftCoreM do
  let fresh ← getEnv
  let initial ← getProvenanceCounters
  unless initial.memoHits == 0 && initial.visits == 0 do
    throwError "[FAIL] IsolationFreshEnvironment: imported cache"
  for warmFirst in [false, true] do
    for (option, budget) in [(`provenanceDefEqLimit, 0), (`provenanceExpressionLimit, 0),
        (`provenanceExpressionLimit, 64)] do
      withEnv fresh do
        let clean := mkConst ``AllowlistBoundaries.plain
        if warmFirst then
          let _ ← readoutClosureCurrent ``AllowlistBoundaries.target clean
          pure ()
        let exhausted ← withOptions (·.set option (budget : Nat)) <|
          readoutClosureCurrent ``AllowlistBoundaries.target clean
        unless exhausted == (false, none) do
          throwError "[FAIL] IsolationIncomplete: warm={warmFirst} option={option} budget={budget} result={exhausted}"
        let recovered ← readoutClosureCurrent ``AllowlistBoundaries.target clean
        unless !recovered.1 && recovered.2.isSome do
          throwError "[FAIL] IsolationRecovery: warm={warmFirst} option={option} budget={budget} result={recovered}"
        let _ ← readoutClosureCurrent ``AllowlistBoundaries.target clean
        let warmed ← getProvenanceCounters
        unless warmed.memoHits > 0 do
          throwError "[FAIL] IsolationWarmCache: no actual summary reuse"
        logInfo m!"[PASS] IsolationRecovery/warm={warmFirst}/option={option}/budget={budget}"
  withEnv fresh do
    let proof := mkConst ``AllowlistBoundaries.proofArgument
    let clean ← readoutClosureCurrent ``AllowlistBoundaries.target proof
    let blocked ← readoutClosureCurrent ``AllowlistBoundaries.harmless proof
    let recovered ← readoutClosureCurrent ``AllowlistBoundaries.target proof
    unless !clean.1 && clean.2.isSome && blocked.1 && recovered == clean do
      throwError "[FAIL] IsolationStatementChange: {clean}; {blocked}; {recovered}"
    logInfo "[PASS] IsolationStatementChange"
  withEnv fresh do
    let levels := [.zero, .succ .zero]
    let mut cold := #[]
    for level in levels do
      let result ← withEnv fresh <| readoutClosureCurrent ``universeTarget (mkConst ``Box.mk [level])
      cold := cold.push result
    for i in [1, 0, 1] do
      let result ← readoutClosureCurrent ``universeTarget (mkConst ``Box.mk [levels[i]!])
      unless result == cold[i]! do throwError "[FAIL] IsolationUniverseChange: {i}: {result}; {cold[i]!}"
    unless cold[1]!.1 do throwError "[FAIL] IsolationUniverseChange: target universe admitted"
    logInfo "[PASS] IsolationUniverseChange"
  withEnv fresh do
    let boolType := mkConst ``Bool
    let proofType := mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Nat) (mkNatLit 137) (mkNatLit 137)
    let make := fun domain => mkLambda `index .default (mkConst ``Unit)
      (mkLambda `state .default domain (.bvar 0))
    let clean ← readoutClosureCurrent ``AllowlistBoundaries.target (make boolType)
    let blocked ← readoutClosureCurrent ``AllowlistBoundaries.target (make proofType)
    let recovered ← readoutClosureCurrent ``AllowlistBoundaries.target (make boolType)
    unless !clean.1 && clean.2.isSome && blocked.1 && recovered == clean do
      throwError "[FAIL] IsolationBinderContext: {clean}; {blocked}; {recovered}"
    logInfo "[PASS] IsolationBinderContext"
end ProvenanceIsolation

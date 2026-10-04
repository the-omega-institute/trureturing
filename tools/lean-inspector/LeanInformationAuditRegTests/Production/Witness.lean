import Reg.D5.S0.CayleyGrowth.ConsecutiveFourCycleDiameterRefutation
import Reg.D5.S0.Certificates.Games.PekalaOnlineMajorityFourColourRefutation
import Reg.D5.S3.Analytic.Interpolation.SelfConjugateGridSchurRatioRefutation
import Reg.D5.S3.Combinatorics.Graph.SuvagiyaSignedSquareCycleRefutation
import Reg.D5.S3.Resource.MinimumRetrievalTime
import Reg.D5.S3.Resource.VandermondeHyperbolicRefutation
import Reg.D5.S3.StatisticalMechanics.PaddedGinibreNonHalfIntegerRefutation
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open Lean Meta LeanInformationAudit

run_meta do
  let mut entries := #[]
  for entry in InformationRegistry.entries (← getEnv) do
    let bridge ← getConstInfo entry.realizationName
    if bridge.type.isAppOf RegistrationElaboration.witnessBridgeName then
      entries := entries.push entry
  unless entries.size == 7 do
    throwError "production witness count: actual={entries.size} expected=7"
  for entry in entries do
    let unit ← mkConstWithFreshMVarLevels entry.unitName
    let statement ← mkAppM
      `D5.S3.ConceptDynamics.InformationEscape.TheoremUnit.Statement #[unit]
    unless ← isDefEq statement (← getConstInfo entry.theoremName).type do
      throwError "production witness statement: {entry.theoremName}"
    let some value := (← getConstInfo entry.unitName).value? (allowOpaque := true)
      | throwError "production witness unit: {entry.theoremName}"
    checkWithKernel value
  logInfo "[PASS] seven production witness companions preserve their original statements"

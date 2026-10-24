import Mathlib
import LeanInformationAuditRegAnalysis.SearchReduction.Commands

/-! Publication is fail-closed when either the emitted verdict or a decisive
    GraphReading field is changed after the producer computation. -/
open Lean Meta Elab Command LeanInformationAudit.SearchReduction

private def rejects (name : Name) (observation : Observation) : TermElabM Unit := do
  let accepted ← try
      publish name observation
      pure true
    catch _ => pure false
  unless !accepted do
    throwError s!"publication mutation was accepted: {name}"

run_cmd liftTermElabM do
  rejects `tamperedVerdict {
    target := `tamperedVerdict
    base := .incomplete .undecided
    paired := .incomplete .undecided
    verdict := .bindOnly
    graph? := some ({ } : GraphReading) }
  rejects `tamperedReading {
    target := `tamperedReading
    base := .incomplete .undecided
    paired := .incomplete .undecided
    verdict := .insufficient
    graph? := some ({ graph := {}, presentationCertified := true } : GraphReading) }
  logInfo "publication mutation tests: verdict and decisive reading rejected"

/- Publication must not inherit a request wrapper's recursion limit. -/
run_cmd liftTermElabM <| withOptions (fun opts => opts.set `maxRecDepth (32 : Nat)) do
  let before ← getEnv
  let reading : GraphReading := {
    graph := { vertices := (List.range 128).map fun id => { id } } }
  publish `largePublication {
    target := `largePublication, base := .incomplete .undecided,
    paired := .incomplete .undecided, verdict := .insufficient, graph? := some reading }
  let axioms ← collectAxioms `largePublication.verdictProof
  unless standardAxioms axioms do throwError "large publication has nonstandard axioms"
  logInfo "large GraphReading publication: kernel equality checked"
  let constants ← #[`largePublication.graphReading, `largePublication.verdictProof,
    `largePublication.verdictWithNoHit, `largePublication].mapM getConstInfo
  for _ in [(), ()] do
    withEnv before <| replayPublication constants `largePublication `largePublication
  logInfo "repeated parent publication replay: kernel equalities rechecked"

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

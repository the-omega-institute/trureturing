import LeanInformationAudit.Tests.Projection.E1Projection
import LeanInformationAudit.Projection.ProjectionValidation

open Lean Lean.Elab.Command LeanInformationAudit
open LeanInformationAudit.Tests.Projection

private def checkMutation (change : KernelProjectionRecord → KernelProjectionRecord) :
    CommandElabM Unit := do
  let certified := (projectionFixtureStore.getState (← getEnv))[0]!
  match validateProjectionSnapshot `E1 `catalog certified (change certified) with
  | .ok () => throwError "mutation unexpectedly accepted"
  | .error message => throwError message

/-- error: IE-C039 InvalidGeneratedKernelNode root=E1 catalog=catalog node=duplicate reason=duplicate-extensional-node -/
#guard_msgs in
run_cmd checkMutation fun p =>
  { p with nodes := p.nodes.push { p.nodes[0]! with key := "duplicate" } }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=E1 catalog=catalog component=node:K_:escape_count expected=12 actual=11 -/
#guard_msgs in
run_cmd checkMutation fun p =>
  { p with nodes := p.nodes.set! 0 { p.nodes[0]! with escapeCount := 11 } }

/-- error: IE-C041 IncompleteKernelProjectionBoundary root=E1 catalog=catalog missing=["K_2"] -/
#guard_msgs in
run_cmd checkMutation fun p => { p with nodes := p.nodes.filter (·.key != "K_2") }

/-- error: IE-C042 KernelProjectionCertificateMismatch root=E1 catalog=catalog component=verdict expected="redundant" actual="irredundant" -/
#guard_msgs in
run_cmd checkMutation fun p => { p with verdict := "irredundant" }

#print axioms checkMutation

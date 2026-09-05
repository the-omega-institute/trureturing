import LeanInformationAudit.AnalysisProjection
import LeanInformationAudit.Tests.Projection.KernelLaws

open Lean Lean.Meta Lean.Elab.Command LeanInformationAudit

namespace LeanInformationAudit.Tests.Projection

run_cmd do
  let (analysis, declarations) ← liftTermElabM do
    let value ← mkConstWithFreshMVarLevels ``catalog
    let enum ← ProjectionProof.enumeration (← mkConstWithFreshMVarLevels ``arena) ``arena
    (prepareAnalysisProjection value enum #[``aFst, ``bSnd, ``cId] `AnalysisContract).run #[]
  unless analysis.exclusiveCaptureTotal == 0 do throwError "exclusive total"
  unless analysis.spectrum.map (·.count) == #[0, 0, 8, 4] do throwError "spectrum"
  unless analysis.overlap.map (·.count) == #[8, 4, 8, 8, 8, 12] do throwError "overlap"
  unless analysis.refinement[1]!.comparison == "incomparable" do throwError "refinement"
  unless analysis.equivalenceClasses.size == 3 do throwError "equivalence"
  for declaration in declarations do
    liftCoreM <| addDecl declaration
    for name in declaration.getNames do
      elabCommand (← `(command| #print axioms $(mkIdent name)))

run_cmd do
  let (analysis, declarations) ← liftTermElabM do
    let members := #[``cId, ``bSnd, ``aFst]
    let vector ← ProjectionProof.vector (← members.mapM fun name => do
      mkConstWithFreshMVarLevels name)
    let value ← mkAppM
      ``D5.S3.ConceptDynamics.InformationEscape.Catalog.ofVector #[vector]
    let enum ← ProjectionProof.enumeration (← mkConstWithFreshMVarLevels ``arena) ``arena
    (prepareAnalysisProjection value enum members `ReverseAnalysisContract).run #[]
  unless analysis.overlap.size == 6 && analysis.overlap.all (fun row =>
      row.left == row.right || row.left.toString < row.right.toString) do
    throwError "overlap triangle must follow canonical Name order"
  for declaration in declarations do
    liftCoreM <| addDecl declaration
    for name in declaration.getNames do
      elabCommand (← `(command| #print axioms $(mkIdent name)))

end LeanInformationAudit.Tests.Projection

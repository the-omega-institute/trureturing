import Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand

namespace Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber
noncomputable section
open _root_.D5.S3.Observer.Separation.BooleanRankThreeFiber
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Lean in
run_meta do
  let some row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Observer.Separation.BooleanRankThreeFiber.result
    | throwError "rank-three registration record is absent"
  let .declaredValidated certificate := row.result
    | throwError "rank-three registration is not declaredValidated"
  unless certificate.escape.bridgeKind == "source-equivalence" do
    throwError "rank-three registration lacks exact source equivalence"
  unless !certificate.evidenceRef.isEmpty && certificate.sourceBinding.isSome do
    throwError "rank-three registration lacks source binding evidence"
  logInfo m!"RANK_THREE_BINDING {certificate.evidenceRef} {certificate.escape.bridgeKind} {certificate.sourceBinding.get!}"

end
end Reg.D5.S3.Observer.Separation.BooleanRankThreeFiber

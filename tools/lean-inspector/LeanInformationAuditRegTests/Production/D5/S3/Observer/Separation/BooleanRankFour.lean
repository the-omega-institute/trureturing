import Reg.D5.S3.Observer.Separation.BooleanRankFour
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

namespace Reg.D5.S3.Observer.Separation.BooleanRankFour
noncomputable section
open _root_.D5.S3.Observer.Separation.BooleanRankFour
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Lean in
run_meta do
  let some row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Observer.Separation.BooleanRankFour.result
    | throwError "BooleanRankFour registration is absent"
  match row.result with
  | .declaredValidated certificate =>
    unless certificate.sourceBinding.isSome && !certificate.evidenceRef.isEmpty &&
        certificate.escape.bridgeKind == "source-equivalence" do
      throwError "BooleanRankFour current source binding evidence is incomplete"
    logInfo m!"BOOLEAN_RANK_FOUR_DECLARED_VALIDATED {certificate.evidenceRef}"
    logInfo m!"{certificate.sourceBinding.get!}"
  | .declaredUnresolved diagnostic =>
    throwError "BooleanRankFour registration unresolved: {diagnostic}"
  | .undeclared => throwError "BooleanRankFour registration undeclared"

end
end Reg.D5.S3.Observer.Separation.BooleanRankFour

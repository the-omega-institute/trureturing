import Reg.D5.S0.Automata.BoundedStateSampleCompactness
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

namespace Reg.D5.S0.Automata.BoundedStateSampleCompactness
open _root_.D5.S0.Automata.DFAOStateLowerBound
open _root_.D5.S0.Automata.FiniteSampleRestriction
open _root_.D5.S0.Automata.BoundedStateSampleCompactness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S0.Automata.BoundedStateSampleCompactness.bounded_state_sample_compactness
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "bounded-state compactness registration is not declaredValidated"

end Reg.D5.S0.Automata.BoundedStateSampleCompactness

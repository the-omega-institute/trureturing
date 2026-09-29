import Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand

open _root_.D5.S3.Arith.FibonacciAtomic.MertensBoundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter Asymptotics
open scoped BigOperators
namespace Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary
noncomputable section
open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Arith.FibonacciAtomic.MertensBoundary.power_bounds_iff
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "Mertens boundary registration is not declaredValidated"

end
end Reg.D5.S3.Arith.FibonacciAtomic.MertensBoundary

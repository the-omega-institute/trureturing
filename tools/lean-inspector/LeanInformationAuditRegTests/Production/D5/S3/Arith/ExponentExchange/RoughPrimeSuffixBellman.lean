import Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open _root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.rough_prime_suffix_complete
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "rough prime suffix registration is not declaredValidated"

open Lean in
run_meta do
  for name in [
      `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.feasible_finite,
      `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.bellman_complete,
      `D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.suffix_prime_factors] do
    let row := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == name
    unless row.any (fun record => match record.result with
        | .declaredValidated _ => true | _ => false) do
      throwError "{name} registration is not declaredValidated"

end Reg.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman

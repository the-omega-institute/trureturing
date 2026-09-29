import Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization
import LeanInformationAudit.Census.Query
import LeanInformationAudit.SealCommand

open _root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
open _root_.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization
open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.forced_core_normalization
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "forced core normalization registration is not declaredValidated"

end Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization

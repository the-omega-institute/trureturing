import Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

namespace Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel
open LeanInformationAudit

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName == `D5.S3.Arith.GoldenResource.PrefixDeficitKernel.result
  unless row.any (fun record => match record.result with
      | .declaredValidated _ => true | _ => false) do
    throwError "Prefix deficit kernel registration is not declaredValidated"

end Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel

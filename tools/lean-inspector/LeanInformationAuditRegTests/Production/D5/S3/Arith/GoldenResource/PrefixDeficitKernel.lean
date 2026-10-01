import Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

namespace Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel
open LeanInformationAudit

open Lean in
run_meta do
  let some record := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == `D5.S3.Arith.GoldenResource.PrefixDeficitKernel.result &&
        record.occurrence.key.registrationModule == `Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel
    | throwError "original prefix deficit occurrence absent"
  let .declaredValidated cert := record.result
    | throwError "registration failed: {(← TemplateBinding.recordJson record).compress}"
  logInfo m!"declared_validated D5.S3.Arith.GoldenResource.PrefixDeficitKernel.result {cert.evidenceRef}"

end Reg.D5.S3.Arith.GoldenResource.PrefixDeficitKernel

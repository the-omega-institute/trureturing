import Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

/-! The report's replay of the recorded inputs assesses the registrations of
`Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion`;
the registration module itself only records them. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
open Lean in
run_meta do
  for target in #[`D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_common_depth_fullness,
      `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_nonconverse,
      `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_future_residue_equivalence] do
    let some record := (LeanInformationAudit.TemplateBinding.records (← getEnv)).find? fun record =>
        record.occurrence.key.theoremName == target &&
          record.occurrence.key.registrationModule == `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
      | throwError "original occurrence absent: {target}"
    let .declaredValidated cert := record.result
      | throwError "registration failed: {(← LeanInformationAudit.TemplateBinding.recordJson record).compress}"
    logInfo m!"declared_validated {target} {cert.evidenceRef}"

end Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion

import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.ImportClosureProducer

open LeanInformationAudit
open LeanInformationAudit.Tests.ImportClosureProducer

namespace LeanInformationAudit.Tests.ExpectedManifestStatementMismatch

expect_information_occurrence importedTheorem
  in objectArena
  from "LeanInformationAudit.Tests.ImportClosureProducer"
  statement_id "sha256:stale"

/-- error: IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.ExpectedManifestStatementMismatch catalog=registry-snapshot component=statement-identities expected=["LeanInformationAudit.Tests.ImportClosureProducer.objectArena/LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem=sha256:stale"] actual=["LeanInformationAudit.Tests.ImportClosureProducer.objectArena/LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem=sha256:d9f7df12989a2b8aeb3e0dbfc1b5da42678137d8e94c7ba9f097d7f74ae08f45"] -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.ExpectedManifestStatementMismatch

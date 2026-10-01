import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Occurrence.ImportClosureProducer
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open LeanInformationAudit

namespace LeanInformationAudit.Tests.ExpectedManifestAddition

/-- error: IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.Occurrence.ExpectedManifestAddition catalog=registry-snapshot component=member-set expected=[] actual=["LeanInformationAudit.Tests.ImportClosureProducer.objectArena/LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem"] -/
#guard_msgs (error) in
test_assess in #seal_information_theory

end LeanInformationAudit.Tests.ExpectedManifestAddition

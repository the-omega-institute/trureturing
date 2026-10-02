import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.ExpectedManifestOmission

def objectArena : Arena := Arena.ofFintype Bool

theorem expectedButUnregistered : True := trivial

test_assess in expect_information_occurrence expectedButUnregistered
  in objectArena
  from "LeanInformationAudit.Tests.Occurrence.ExpectedManifestOmission"

/-- error: IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.Occurrence.ExpectedManifestOmission catalog=registry-snapshot component=member-set expected=["LeanInformationAudit.Tests.ExpectedManifestOmission.objectArena/LeanInformationAudit.Tests.ExpectedManifestOmission.expectedButUnregistered"] actual=[] -/
#guard_msgs (error) in
test_assess in #seal_information_theory

end LeanInformationAudit.Tests.ExpectedManifestOmission

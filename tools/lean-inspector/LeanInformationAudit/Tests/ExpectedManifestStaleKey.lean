import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.ImportClosureProducer

open LeanInformationAudit
open LeanInformationAudit.Tests.ImportClosureProducer
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.ExpectedManifestStaleKey

def staleArena : Arena := Arena.ofFintype Bool

expect_information_occurrence importedTheorem
  in staleArena
  from "LeanInformationAudit.Tests.ImportClosureProducer"

/-- error: IE-C028 AnalysisCertificateMismatch root=LeanInformationAudit.Tests.ExpectedManifestStaleKey catalog=registry-snapshot component=member-set expected=["LeanInformationAudit.Tests.ExpectedManifestStaleKey.staleArena/LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem"] actual=["LeanInformationAudit.Tests.ImportClosureProducer.objectArena/LeanInformationAudit.Tests.ImportClosureProducer.importedTheorem"] -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.ExpectedManifestStaleKey

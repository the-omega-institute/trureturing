import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.SealCollisionProducerA
import LeanInformationAudit.Tests.SealCollisionProducerB

namespace LeanInformationAudit.Tests.SealCollision

/-! Removing `validatePersistedEntry` makes this exact duplicate diagnostic disappear. -/

/-- error: IE-C002 DuplicateRegistration:
LeanInformationAudit.Tests.SealCollisionFixture.target -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.SealCollision

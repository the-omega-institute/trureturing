import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.SealCollisionProducerA
import LeanInformationAudit.Tests.SealCollisionProducerB

set_option linter.style.longLine false

namespace LeanInformationAudit.Tests.SealCollision

/-! Removing `validatePersistedEntry` makes this exact duplicate diagnostic disappear. -/

expect_information_occurrence
  _root_.LeanInformationAudit.Tests.SealCollisionFixture.target
  in _root_.LeanInformationAudit.Tests.SealCollisionFixture.arena
  from "LeanInformationAudit.Tests.SealCollisionProducerA"

expect_information_occurrence
  _root_.LeanInformationAudit.Tests.SealCollisionFixture.target
  in _root_.LeanInformationAudit.Tests.SealCollisionFixture.arena
  from "LeanInformationAudit.Tests.SealCollisionProducerB"

/-- error: IE-C002 DuplicateRegistration object_arena=LeanInformationAudit.Tests.SealCollisionFixture.arena theorem_name=LeanInformationAudit.Tests.SealCollisionFixture.target registration_modules=["LeanInformationAudit.Tests.SealCollisionProducerA","LeanInformationAudit.Tests.SealCollisionProducerB"] count=2 -/
#guard_msgs (error) in
#seal_information_theory

end LeanInformationAudit.Tests.SealCollision

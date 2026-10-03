import LeanInformationAudit.SealCommand
import LeanInformationAudit.Tests.SealCollisionProducerA
import LeanInformationAudit.Tests.SealCollisionProducerB
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

set_option linter.style.longLine false

namespace LeanInformationAudit.Tests.SealCollision

/-! Removing `validatePersistedEntry` makes this exact duplicate diagnostic disappear. -/

test_assess in expect_information_occurrence
  _root_.LeanInformationAudit.Tests.SealCollisionFixture.target
  in _root_.LeanInformationAudit.Tests.SealCollisionFixture.arena
  from "LeanInformationAudit.Tests.SealCollisionProducerA"

test_assess in expect_information_occurrence
  _root_.LeanInformationAudit.Tests.SealCollisionFixture.target
  in _root_.LeanInformationAudit.Tests.SealCollisionFixture.arena
  from "LeanInformationAudit.Tests.SealCollisionProducerB"

/-- error: IE-C002 DuplicateRegistration object_arena=LeanInformationAudit.Tests.SealCollisionFixture.arena theorem_name=LeanInformationAudit.Tests.SealCollisionFixture.target registration_modules=["LeanInformationAudit.Tests.SealCollisionProducerA","LeanInformationAudit.Tests.SealCollisionProducerB"] count=2 -/
#guard_msgs (error) in
test_assess in #seal_information_theory

end LeanInformationAudit.Tests.SealCollision

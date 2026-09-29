import LeanInformationAudit.Tests.SealCollisionBase

open LeanInformationAudit

run_cmd registerValidatedEntry (← Lean.getEnv).header.mainModule {
  theoremName := `LeanInformationAudit.Tests.SealCollisionFixture.target
  unitName := `LeanInformationAudit.Tests.SealCollisionFixture.persistedUnit
  arenaName := `LeanInformationAudit.Tests.SealCollisionFixture.arena
  realizationName := `LeanInformationAudit.Tests.SealCollisionFixture.fixtureRealization
}

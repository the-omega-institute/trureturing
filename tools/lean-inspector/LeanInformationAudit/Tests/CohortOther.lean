import LeanInformationAuditInterface.Syntax
import LeanInformationAudit.Tests.CohortArena

/-! A second unrelated peer: one registration without a declared readout. -/

namespace LeanInformationAudit.Tests.CohortOther
open D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit.Tests.CohortArena

local instance : DecidableEq arena.State := instDecidableEqBool

theorem statement : arena.Law good := rfl
theorem bridge : LegacyPrimitiveRealization arena (arena.Law good) good := ⟨Iff.rfl⟩

register_information_theorem statement in arena primitives good.toPrimitiveBundle
  realization bridge variation lawVariation sensitivity slotSensitivity

end LeanInformationAudit.Tests.CohortOther

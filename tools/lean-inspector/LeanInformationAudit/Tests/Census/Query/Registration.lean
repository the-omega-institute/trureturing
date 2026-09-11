import LeanInformationAudit.Tests.Census.Query.Source

namespace LeanInformationAudit.Tests.Census.Query

open LeanInformationAudit LeanInformationAudit.Tests.SealSuccess
open D5.S3.ConceptDynamics.InformationEscape

local instance : DecidableEq t001Arena.State := t001Arena.toArena.stateDecidableEq

theorem legacy : LegacyPrimitiveRealization t001Arena
    (t001Arena.Law idRealization) idRealization := ⟨Iff.rfl⟩

register_information_theorem target in t001Arena
  primitives idRealization.toPrimitiveBundle realization legacy

end LeanInformationAudit.Tests.Census.Query

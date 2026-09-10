import LeanInformationAudit.Tests.SealSuccess

namespace LeanInformationAudit.Tests.Census.Query

open D5.S3.ConceptDynamics.InformationEscape
open LeanInformationAudit.Tests.SealSuccess

theorem target : t001Arena.Law idRealization := by trivial

theorem nondegenerate : t001Arena.toArena.Nondegenerate := by decide

def enumeration : Arena.StateEnumeration t001Arena.toArena where
  states := [false, true]
  nodup := by change ([false, true] : List Bool).Nodup; decide
  complete := by change ([false, true] : List Bool).toFinset = Finset.univ; decide

end LeanInformationAudit.Tests.Census.Query

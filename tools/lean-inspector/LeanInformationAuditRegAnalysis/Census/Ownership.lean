import Lean

namespace LeanInformationAudit.CensusOwnership

open Lean

/-- Realized reserved theorems can occur in several modules. The first-import
index is provenance for lookup, not a unique ownership authority. -/
def moduleContainsTheorem (data : ModuleData) (info : ConstantInfo) : Bool :=
  info.isTheorem && data.constNames.contains info.name &&
    data.constants.any (fun localInfo => localInfo.name == info.name && localInfo.isTheorem &&
      localInfo.type == info.type && localInfo.levelParams == info.levelParams)


end LeanInformationAudit.CensusOwnership

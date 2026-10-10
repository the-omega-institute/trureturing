import LeanInformationAudit.InputTypes

namespace LeanInformationAudit
open Lean

/-- A closed catalog and the canonical theorem-to-index assignment used by the seal. -/
structure CatalogUnitRecord where
  theoremName : Name
  unitName : Name
  realizationName : Name
  registrationModuleName : Name
  index : Nat
  deriving Inhabited, BEq

structure CatalogRecord where
  rootId : Name
  catalogId : CatalogId
  catalogKind : CatalogKind
  arenaName : Name
  catalogName : Name
  units : Array CatalogUnitRecord
  localSealNames : Bool
  deriving Inhabited, BEq

/-- The exact imported registration membership of a kernel-checked seal.
Mathematical obligations remain in Reg, without report statistics. -/
structure SealArenaRecord where
  catalog : CatalogRecord
  compiledEvidence : Bool := false
  deriving Inhabited, BEq

end LeanInformationAudit
